import Mettapedia.GSLT.LanguageDef.OrderedMatchMachineExactness
import Mettapedia.GSLT.LanguageDef.BindingDecisionAdequacy

/-!
# Adequacy of the ordered-match machine language for the fused evaluator

The reference machine of the ordered-match machine language reaches a result
from a fused program on a subject exactly when the fused program's evaluator
lists that result, with every leaf run by binding-decision matching, ordered
premise evaluation through the source relation environment, and template
instantiation.  Through the exactness theorem this transfers to the language
itself: the language's own multi-step reduction from an encoded program to
an encoded result is membership in the evaluator's output, and, for programs
fused from first-order rule plans, membership in the plan interpreter's
output.  The language is therefore the evaluator of fused decision programs,
not a description beside it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan PremisePlan RulePlan runPremisePlans patternPlansWork)
open Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix (lowerSubject)
open Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
  (isBoundAt isConstructorOf eval_checkBound_eq eval_checkConstructor_eq mem_eval_join_iff)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

variable (relations : RelationEnv) (source : LanguageDef)

/-! ## Reachability in the reference machine -/

/-- One machine step as a relation. -/
def MachineStep (state next : MachineState) : Prop :=
  next ∈ machineStep relations source state

/-- Finitely many machine steps. -/
def Reaches : MachineState → MachineState → Prop :=
  Relation.ReflTransGen (MachineStep relations source)

theorem machineStep_done (result : Pattern) : machineStep relations source (.done result) = [] := rfl

/-- A run from a non-terminal state to a result goes through one of the
state's successors. -/
theorem reaches_done_iff_succ {state : MachineState}
    (notDone : ∀ result, state ≠ .done result) (result : Pattern) :
    Reaches relations source state (.done result) ↔
      ∃ next ∈ machineStep relations source state,
        Reaches relations source next (.done result) := by
  constructor
  · intro run
    rcases Relation.ReflTransGen.cases_head run with equal | ⟨next, step, rest⟩
    · exact absurd equal (notDone result)
    · exact ⟨next, step, rest⟩
  · rintro ⟨next, step, rest⟩
    exact Relation.ReflTransGen.head step rest

/-- A result reaches only itself. -/
theorem reaches_done_done_iff (value result : Pattern) :
    Reaches relations source (.done value) (.done result) ↔ result = value := by
  constructor
  · intro run
    rcases Relation.ReflTransGen.cases_head run with equal | ⟨next, step, _⟩
    · exact (MachineState.done.inj equal).symm
    · change next ∈ machineStep relations source (.done value) at step
      simp [machineStep_done] at step
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-! ## Instantiation -/

/-- What the instantiation continuation makes of a finished value. -/
def runInstantiateKont (bindings : Bindings) : List InstantiateFrame → Pattern → Pattern
  | [], value => value
  | .argument constructor accumulated remaining :: rest, value =>
      runInstantiateKont bindings rest
        (.apply constructor
          ((value :: accumulated).reverse ++ remaining.map (PatternPlan.instantiate bindings)))

/-- Remaining instantiation work stored in a continuation. -/
def kontWork : List InstantiateFrame → Nat
  | [] => 0
  | .argument _ _ remaining :: rest => 4 * patternPlansWork remaining + 2 + kontWork rest

private theorem instantiation_reaches (result : Pattern) : ∀ n : Nat,
    (∀ (template : PatternPlan) (bindings : Bindings) (kont : List InstantiateFrame),
      4 * template.work + kontWork kont ≤ n →
        (Reaches relations source (.instantiate template bindings kont) (.done result) ↔
          result = runInstantiateKont bindings kont (template.instantiate bindings))) ∧
    (∀ (constructor : String) (accumulated : List Pattern) (remaining : List PatternPlan)
        (bindings : Bindings) (kont : List InstantiateFrame),
      4 * patternPlansWork remaining + kontWork kont + 3 ≤ n →
        (Reaches relations source
            (.instantiateArguments constructor accumulated remaining bindings kont)
            (.done result) ↔
          result = runInstantiateKont bindings kont
            (.apply constructor
              (accumulated.reverse ++ remaining.map (PatternPlan.instantiate bindings))))) ∧
    (∀ (value : Pattern) (bindings : Bindings) (kont : List InstantiateFrame),
      kontWork kont + 2 ≤ n →
        (Reaches relations source (.instantiated value bindings kont) (.done result) ↔
          result = runInstantiateKont bindings kont value)) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro template bindings kont bound
        have := PatternPlan.work_pos template
        omega
      · intro constructor accumulated remaining bindings kont bound
        omega
      · intro value bindings kont bound
        omega
  | succ n inductionHypothesis =>
      obtain ⟨templateHypothesis, argumentsHypothesis, valueHypothesis⟩ := inductionHypothesis
      refine ⟨?_, ?_, ?_⟩
      · intro template bindings kont bound
        cases template with
        | metavariable name =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [valueHypothesis (lookupOrVariable bindings name) bindings kont
              (by simp [PatternPlan.work] at bound; omega)]
            rw [instantiate_metavariable]
        | bound index =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [valueHypothesis (.bvar index) bindings kont
              (by simp [PatternPlan.work] at bound; omega)]
            rw [PatternPlan.instantiate]
        | application constructor arguments =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [argumentsHypothesis constructor [] arguments bindings kont
              (by simp [PatternPlan.work] at bound; omega)]
            rw [PatternPlan.instantiate]
            simp
      · intro constructor accumulated remaining bindings kont bound
        cases remaining with
        | nil =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [valueHypothesis (.apply constructor accumulated.reverse) bindings kont
              (by simp [patternPlansWork] at bound; omega)]
            simp
        | cons template templates =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [templateHypothesis template bindings (.argument constructor accumulated templates :: kont)
              (by simp [patternPlansWork, kontWork] at bound ⊢; omega)]
            simp [runInstantiateKont, List.reverse_cons, List.append_assoc]
      · intro value bindings kont bound
        cases kont with
        | nil =>
            rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
            simp only [machineStep, List.mem_singleton, exists_eq_left]
            rw [reaches_done_done_iff]
            rfl
        | cons frame rest =>
            cases frame with
            | argument constructor accumulated remaining =>
                rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
                simp only [machineStep, List.mem_singleton, exists_eq_left]
                rw [argumentsHypothesis constructor (value :: accumulated) remaining bindings rest
                  (by simp [kontWork] at bound; omega)]
                rfl

/-- Instantiating a template under a continuation reaches exactly the value
the continuation makes of the instantiated template. -/
theorem reaches_instantiate_iff (template : PatternPlan) (bindings : Bindings)
    (kont : List InstantiateFrame) (result : Pattern) :
    Reaches relations source (.instantiate template bindings kont) (.done result) ↔
      result = runInstantiateKont bindings kont (template.instantiate bindings) :=
  (instantiation_reaches relations source result _).1 template bindings kont le_rfl

/-! ## Premises -/

/-- Premise evaluation reaches exactly the instantiations of the template
under the ordered premise results. -/
theorem reaches_premises_iff (queries : List PremisePlan) :
    ∀ (template : PatternPlan) (bindings : Bindings) (result : Pattern),
      Reaches relations source (.premises queries template bindings) (.done result) ↔
        ∃ final ∈ runPremisePlans relations source queries bindings,
          result = template.instantiate final := by
  induction queries with
  | nil =>
      intro template bindings result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [reaches_instantiate_iff]
      simp [runPremisePlans, runInstantiateKont]
  | cons query queries inductionHypothesis =>
      intro template bindings result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_map, runPremisePlans, List.mem_flatMap]
      constructor
      · rintro ⟨next, ⟨extended, member, rfl⟩, run⟩
        obtain ⟨final, finalMember, equal⟩ := (inductionHypothesis template extended result).mp run
        exact ⟨final, ⟨extended, member, finalMember⟩, equal⟩
      · rintro ⟨final, ⟨extended, member, finalMember⟩, equal⟩
        exact ⟨.premises queries template extended, ⟨extended, member, rfl⟩,
          (inductionHypothesis template extended result).mpr ⟨final, finalMember, equal⟩⟩

/-! ## Matching -/

/-- Matching reaches a result exactly through some binding the decision
evaluator lists, returned to the continuation. -/
theorem reaches_bdRun_iff (decision : Decision) :
    ∀ (subject : Pattern) (kont : List Frame) (result : Pattern),
      Reaches relations source (.bdRun decision subject kont) (.done result) ↔
        ∃ bindings ∈ decision.eval subject,
          Reaches relations source (.bdRet bindings subject kont) (.done result) := by
  induction decision with
  | succeed =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, Decision.eval]
  | capture path name =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      cases projection : path.project? subject with
      | none => simp [machineStep, projection, Decision.eval]
      | some focused => simp [machineStep, projection, Decision.eval]
  | checkBound path expected =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion),
        eval_checkBound_eq]
      cases projection : path.project? subject with
      | none => simp [machineStep, projection]
      | some focused =>
          cases bound : isBoundAt focused expected <;> simp [machineStep, projection, bound]
  | checkConstructor path expected arity children inductionHypothesis =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion),
        eval_checkConstructor_eq]
      cases projection : path.project? subject with
      | none => simp [machineStep, projection]
      | some focused =>
          cases constructorTest : isConstructorOf focused expected arity with
          | false => simp [machineStep, projection, constructorTest]
          | true =>
              simp only [machineStep, projection, constructorTest, if_true, List.mem_singleton,
                exists_eq_left]
              exact inductionHypothesis subject kont result
  | join head tail headHypothesis tailHypothesis =>
      intro subject kont result
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [headHypothesis]
      constructor
      · rintro ⟨headBindings, headMember, run⟩
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)] at run
        simp only [machineStep, List.mem_singleton, exists_eq_left] at run
        rw [tailHypothesis] at run
        obtain ⟨tailBindings, tailMember, run⟩ := run
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)] at run
        cases merge : mergeBindings headBindings tailBindings with
        | none => simp [machineStep, merge] at run
        | some merged =>
            simp only [machineStep, merge, List.mem_singleton, exists_eq_left] at run
            exact ⟨merged, (mem_eval_join_iff head tail subject merged).mpr
              ⟨headBindings, headMember, tailBindings, tailMember, merge⟩, run⟩
      · rintro ⟨merged, mergedMember, run⟩
        obtain ⟨headBindings, headMember, tailBindings, tailMember, merge⟩ :=
          (mem_eval_join_iff head tail subject merged).mp mergedMember
        refine ⟨headBindings, headMember, ?_⟩
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, List.mem_singleton, exists_eq_left]
        rw [tailHypothesis]
        refine ⟨tailBindings, tailMember, ?_⟩
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, merge, List.mem_singleton, exists_eq_left]
        exact run

/-- The frame after matching hands the bindings to premise evaluation. -/
theorem reaches_bdRet_afterMatch_iff (bindings : Bindings) (subject : Pattern)
    (premises : List PremisePlan) (template : PatternPlan) (kont : List Frame) (result : Pattern) :
    Reaches relations source (.bdRet bindings subject (.afterMatch premises template :: kont))
        (.done result) ↔
      Reaches relations source (.premises premises template bindings) (.done result) := by
  rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
  simp [machineStep]

/-! ## Leaves -/

/-- What one leaf produces on a subject: matched bindings, then ordered
premises, then the instantiated template.  This is the plan interpreter's
shape with the binding decision in place of the pattern plan. -/
def runLeaf (subject : Pattern) (leaf : Leaf) : List Pattern :=
  (leaf.plan.decision.eval subject).flatMap fun bindings =>
    (runPremisePlans relations source leaf.plan.premises bindings).map
      leaf.plan.template.instantiate

/-- Running a leaf reaches exactly its results. -/
theorem reaches_leaf_iff (leaf : Leaf) (subject result : Pattern) :
    Reaches relations source
        (.bdRun leaf.plan.decision subject [.afterMatch leaf.plan.premises leaf.plan.template])
        (.done result) ↔
      result ∈ runLeaf relations source subject leaf := by
  rw [reaches_bdRun_iff]
  simp only [runLeaf, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨bindings, member, run⟩
    rw [reaches_bdRet_afterMatch_iff, reaches_premises_iff] at run
    obtain ⟨final, finalMember, equal⟩ := run
    exact ⟨bindings, member, final, finalMember, equal.symm⟩
  · rintro ⟨bindings, member, final, finalMember, equal⟩
    refine ⟨bindings, member, ?_⟩
    rw [reaches_bdRet_afterMatch_iff, reaches_premises_iff]
    exact ⟨final, finalMember, equal.symm⟩

/-! ## The structural prefilter -/

mutual
  def matrixPatternSize : MatrixPattern → Nat
    | .wildcard => 1
    | .node _ children => 1 + patternsSize children

  def patternsSize : List MatrixPattern → Nat
    | [] => 0
    | pattern :: patterns => matrixPatternSize pattern + patternsSize patterns
end

theorem patternsSize_append (first second : List MatrixPattern) :
    patternsSize (first ++ second) = patternsSize first + patternsSize second := by
  induction first with
  | nil => simp [patternsSize]
  | cons pattern patterns inductionHypothesis =>
      simp only [List.cons_append, patternsSize, inductionHypothesis]
      omega

/-- The prefilter reaches a result exactly when the residual patterns match
the lowered cursor structurally and the leaf produces the result. -/
theorem reaches_prefilter_iff (leaf : Leaf) (subject result : Pattern) :
    ∀ (patterns : List MatrixPattern) (cursor : List Pattern),
      Reaches relations source (.prefilter patterns cursor leaf subject) (.done result) ↔
        (OPM.structuralMatchList patterns (cursor.map lowerSubject) = true ∧
          result ∈ runLeaf relations source subject leaf)
  | [], [] => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [reaches_leaf_iff]
      simp [OPM.structuralMatchList]
  | [], focused :: cursor => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, OPM.structuralMatchList]
  | .wildcard :: patterns, [] => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, OPM.structuralMatchList]
  | .wildcard :: patterns, focused :: cursor => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep, List.mem_singleton, exists_eq_left]
      rw [reaches_prefilter_iff leaf subject result patterns cursor]
      simp [OPM.structuralMatchList, OPM.structuralMatch]
  | .node head children :: patterns, [] => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp [machineStep, OPM.structuralMatchList]
  | .node head children :: patterns, focused :: cursor => by
      rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
      simp only [machineStep]
      by_cases keyTest : subjectKey focused = (⟨head, children.length⟩ : Key)
      · rw [if_pos keyTest]
        simp only [List.mem_singleton, exists_eq_left]
        rw [reaches_prefilter_iff leaf subject result (children ++ patterns)
          (subjectChildren focused ++ cursor)]
        simp only [subjectKey,
          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.ConstructorKey.mk.injEq]
          at keyTest
        obtain ⟨headEqual, lengthEqual⟩ := keyTest
        rw [List.map_cons, List.map_append, lowerSubject_eq focused, OPM.structuralMatchList,
          OPM.structuralMatch,
          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.structuralMatchList_append
            children patterns _ _ (by simp [lengthEqual])]
        simp [headEqual]
      · rw [if_neg keyTest]
        simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
        intro structural
        exfalso
        rw [List.map_cons, lowerSubject_eq focused, OPM.structuralMatchList, OPM.structuralMatch]
          at structural
        by_cases headEqual : head = subjectHead focused
        · have lengthDifferent : (subjectChildren focused).length ≠ children.length := by
            intro lengthEqual
            apply keyTest
            simp [subjectKey, headEqual, lengthEqual]
          rw [Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.structuralMatchList_eq_false_of_length_ne
            children _ (by simpa using lengthDifferent.symm)] at structural
          simp at structural
        · simp [headEqual] at structural
termination_by patterns _ => patternsSize patterns
decreasing_by
  all_goals simp [patternsSize, matrixPatternSize, patternsSize_append]

/-! ## Programs -/

mutual
  /-- Running a program reaches a result exactly when the fused evaluator
  lists it, every leaf run by the machine's leaf semantics. -/
  theorem reaches_run_iff :
      ∀ (program : Program) (subject : Pattern) (cursor : List Pattern) (result : Pattern),
        Reaches relations source (.run program subject cursor) (.done result) ↔
          result ∈ program.evalAll (runLeaf relations source subject) (cursor.map lowerSubject)
    | .failure, subject, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp [machineStep, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, subject, [], result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp [machineStep, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, subject, focused :: cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, List.mem_singleton, exists_eq_left]
        rw [reaches_run_iff next subject cursor result]
        simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .tryRule leaf patterns onFailure, subject, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [
          machineStep, List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or,
          exists_eq_left]
        rw [reaches_prefilter_iff relations source leaf subject result patterns cursor,
          reaches_run_iff onFailure subject cursor result]
        simp only [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        by_cases structural : OPM.structuralMatchList patterns (cursor.map lowerSubject) = true
        · simp [structural]
        · simp [structural]
    | .switch branches default, subject, [], result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep, List.mem_singleton, exists_eq_left]
        rw [reaches_run_iff default subject [] result]
        simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .switch branches default, subject, focused :: cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [
          machineStep, List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or,
          exists_eq_left]
        rw [reaches_run_iff default subject (focused :: cursor) result,
          reaches_dispatch_iff branches subject focused cursor result]
        rw [List.map_cons, lowerSubject_eq focused]
        simp only [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll,
          List.mem_append, List.length_map, List.map_append]
        rw [or_comm]
        rfl
  /-- Dispatching on the focused subject's key reaches a result exactly when
  the matching branch's evaluation lists it. -/
  theorem reaches_dispatch_iff :
      ∀ (branches : Branches) (subject focused : Pattern) (cursor : List Pattern)
        (result : Pattern),
        Reaches relations source (.dispatch branches subject focused cursor) (.done result) ↔
          result ∈ Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll
            (runLeaf relations source subject) (subjectKey focused)
            ((subjectChildren focused ++ cursor).map lowerSubject) branches
    | .nil, subject, focused, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp [machineStep,
          Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll]
    | .cons key program rest, subject, focused, cursor, result => by
        rw [reaches_done_iff_succ relations source (fun _ => MachineState.noConfusion)]
        simp only [machineStep]
        by_cases keyTest : subjectKey focused = key
        · rw [if_pos keyTest]
          simp only [List.mem_singleton, exists_eq_left]
          rw [reaches_run_iff program subject (subjectChildren focused ++ cursor) result]
          simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll,
            keyTest]
        · rw [if_neg keyTest]
          simp only [List.mem_singleton, exists_eq_left]
          rw [reaches_dispatch_iff rest subject focused cursor result]
          simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll,
            keyTest]
end

/-- The machine computes exactly the fused evaluator from a fresh cursor. -/
theorem reaches_iff_mem_evalAll (program : Program) (subject result : Pattern) :
    Reaches relations source (.run program subject [subject]) (.done result) ↔
      result ∈ program.evalAll (runLeaf relations source subject) [lowerSubject subject] := by
  simpa using reaches_run_iff relations source program subject [subject] result

/-! ## Transfer to the language -/

/-- Finitely many steps of the language itself. -/
def LanguageReaches : Pattern → Pattern → Prop :=
  Relation.ReflTransGen (ir relations source).semantics.Step

theorem languageReaches_of_reaches {state target : MachineState}
    (run : Reaches relations source state target) :
    LanguageReaches relations source (encodeState state) (encodeState target) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step inductionHypothesis =>
      exact Relation.ReflTransGen.tail inductionHypothesis
        (step_of_machineStep relations source step)

theorem reaches_of_languageReaches {state : MachineState} {target : Pattern}
    (run : LanguageReaches relations source (encodeState state) target) :
    ∃ final : MachineState, target = encodeState final ∧ Reaches relations source state final := by
  induction run with
  | refl => exact ⟨state, rfl, Relation.ReflTransGen.refl⟩
  | tail _ step inductionHypothesis =>
      obtain ⟨middle, rfl, run⟩ := inductionHypothesis
      obtain ⟨next, machineStep, rfl⟩ := machineStep_of_step relations source step
      exact ⟨next, rfl, Relation.ReflTransGen.tail run machineStep⟩

/-- The language reaches an encoded result from an encoded program on a
subject exactly when the fused evaluator lists the result. -/
theorem languageReaches_iff_mem_evalAll (program : Program) (subject result : Pattern) :
    LanguageReaches relations source (encodeState (.run program subject [subject]))
        (encodeState (.done result)) ↔
      result ∈ program.evalAll (runLeaf relations source subject) [lowerSubject subject] := by
  constructor
  · intro run
    obtain ⟨final, equal, machineRun⟩ := reaches_of_languageReaches relations source run
    rw [← encodeState_injective equal] at machineRun
    exact (reaches_iff_mem_evalAll relations source program subject result).mp machineRun
  · intro member
    exact languageReaches_of_reaches relations source
      ((reaches_iff_mem_evalAll relations source program subject result).mpr member)

/-! ## Programs fused from first-order rule plans -/

/-- The machine's plan for a first-order rule plan: the left-hand side
compiled to a binding decision, the premises, and the right-hand side. -/
def toMachinePlan (plan : RulePlan) : MachinePlan :=
  ⟨compile plan.left, plan.premises, plan.right⟩

mutual
  /-- Re-index occurrences and translate leaves of a fused program. -/
  def mapProgram {Rule Plan : Type} (occurrence : Rule → Nat) (plan : Plan → MachinePlan) :
      Fusion.Program Head Rule Plan → Program
    | .failure => .failure
    | .drop next => .drop (mapProgram occurrence plan next)
    | .tryRule compiled patterns onFailure =>
        .tryRule ⟨occurrence compiled.occurrence, plan compiled.plan⟩ patterns
          (mapProgram occurrence plan onFailure)
    | .switch branches default =>
        .switch (mapBranches occurrence plan branches) (mapProgram occurrence plan default)

  def mapBranches {Rule Plan : Type} (occurrence : Rule → Nat) (plan : Plan → MachinePlan) :
      Fusion.Branches Head Rule Plan → Branches
    | .nil => .nil
    | .cons key program rest =>
        .cons key (mapProgram occurrence plan program) (mapBranches occurrence plan rest)
end

mutual
  theorem evalAll_mapProgram {Rule Plan : Type} (occurrence : Rule → Nat)
      (plan : Plan → MachinePlan) (runLeaf : Leaf → List Pattern) :
      ∀ (program : Fusion.Program Head Rule Plan) (subjects : List (OPM.Subject Head)),
        (mapProgram occurrence plan program).evalAll runLeaf subjects =
          program.evalAll (fun compiled => runLeaf ⟨occurrence compiled.occurrence, plan compiled.plan⟩)
            subjects
    | .failure, subjects => by
        simp [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, [] => by
        simp [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
    | .drop next, _ :: subjects => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        exact evalAll_mapProgram occurrence plan runLeaf next subjects
    | .tryRule compiled patterns onFailure, subjects => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        rw [evalAll_mapProgram occurrence plan runLeaf onFailure subjects]
    | .switch branches default, [] => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        exact evalAll_mapProgram occurrence plan runLeaf default []
    | .switch branches default, .node head children :: rest => by
        simp only [mapProgram, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalAll]
        rw [evalBranchAll_mapBranches occurrence plan runLeaf branches,
          evalAll_mapProgram occurrence plan runLeaf default]

  theorem evalBranchAll_mapBranches {Rule Plan : Type} (occurrence : Rule → Nat)
      (plan : Plan → MachinePlan) (runLeaf : Leaf → List Pattern) :
      ∀ (branches : Fusion.Branches Head Rule Plan) (query : Key)
        (subjects : List (OPM.Subject Head)),
        Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll runLeaf query
            subjects (mapBranches occurrence plan branches) =
          Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll
            (fun compiled => runLeaf ⟨occurrence compiled.occurrence, plan compiled.plan⟩)
            query subjects branches
    | .nil, query, subjects => by
        simp [mapBranches, Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll]
    | .cons key program rest, query, subjects => by
        simp only [mapBranches,
          Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll]
        rw [evalAll_mapProgram occurrence plan runLeaf program subjects,
          evalBranchAll_mapBranches occurrence plan runLeaf rest query subjects]
end

/-- The machine's leaf semantics of a translated rule plan is the plan
interpreter. -/
theorem runLeaf_toMachinePlan (subject : Pattern) (occurrence : Nat) (plan : RulePlan) :
    runLeaf relations source subject ⟨occurrence, toMachinePlan plan⟩ =
      plan.run relations source subject := by
  simp [runLeaf, toMachinePlan, RulePlan.run, eval_compile]

/-- For a program fused from first-order rule plans, the language reaches an
encoded result exactly when the fused evaluator with the plan interpreter at
its leaves lists it. -/
theorem languageReaches_mapProgram_iff {Rule : Type}
    (program : Fusion.Program Head Rule RulePlan) (occurrence : Rule → Nat)
    (subject result : Pattern) :
    LanguageReaches relations source
        (encodeState (.run (mapProgram occurrence toMachinePlan program) subject [subject]))
        (encodeState (.done result)) ↔
      result ∈ program.evalAll (fun compiled => compiled.plan.run relations source subject)
        [lowerSubject subject] := by
  rw [languageReaches_iff_mem_evalAll, evalAll_mapProgram]
  simp only [runLeaf_toMachinePlan]

#print axioms reaches_iff_mem_evalAll
#print axioms languageReaches_iff_mem_evalAll
#print axioms languageReaches_mapProgram_iff

end Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
