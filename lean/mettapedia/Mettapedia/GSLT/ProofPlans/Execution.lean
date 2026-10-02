import Mettapedia.GSLT.ProofPlans.Derivations
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine

/-!
# Incremental plan execution is fill-and-resume

Executing a proof plan means running its steps: the procedures that build a
kernel artifact, compute a certificate or a bound, or elaborate a method.  A
plan with open obligations can be executed *incrementally*: the parts that do
not depend on an obligation are executed now, and the rest resumes once the
obligation is discharged.

**Pure total executors.**  A `Model` of the proof definition is a pure, total
executor: every rule application maps the values of its premises to a value of
its conclusion, and obligations are read positionally from the plan's own
ordered context.  Partial execution (`peval`) executes every sub-derivation
that contains no obligation and leaves a residual with holes (`Residual`); no
residual node has only values below it (`peval_reduced`).  Resumption
(`resume`) finishes the residual on values for the obligations, and

* resuming the partial execution on the values of the discharging derivations
  is executing the completed plan (`fill_and_resume`);
* partial discharge resumes in stages (`staged_resume`);
* a plan whose partial execution is already a value gives that value for
  every completion (`determinate`).

**The three conditions, each necessary.**  Fill-and-resume is exact for these
executors because they satisfy the three conditions of evaluation around
holes: the recorded context, purity and termination.  Each condition fails for
an executor of another kind, on a concrete plan of the fixture kernel.

* *Recorded context* (`Contextual`).  A step may change the context of its
  premises, as a step that introduces a hypothesis does.  Resuming an
  obligation in the context recorded at its position agrees with executing the
  completed plan (`Contextual.resume_recorded`); resuming it in the context of
  the whole plan gives another value
  (`Contextual.Controls.topLevel_resumption_differs`).
* *Purity* (`Stateful`, `Relational`).  For a stateful executor without
  effects, incremental execution is execution of the completed plan
  (`Stateful.incremental_ofModel`).  With a counter effect, partial execution
  runs the determined sub-derivation before the discharge, and the values
  differ from the completed plan's (`Stateful.Controls.commutation_fails`); a
  plan whose obligation comes first in execution order agrees
  (`Stateful.Controls.obligation_first_agrees`).  With a nondeterministic step, an
  obligation cited twice is executed twice in the completed plan and once by
  resumption, and the completed plan has a value no resumption produces
  (`Relational.Nondeterminism.completed_value_not_resumed`).
* *Termination* (`Relational`).  For relational (partial, possibly
  nondeterministic) executors, a resumed value is a value of the completed plan
  whenever the discharges terminate (`Relational.runs_bind`), and the converse
  holds for deterministic executors (`Relational.executes_discharge_iff`).  A
  step that ignores the value of its premise predicts a result for every value
  of the obligation, while the completed plan, whose discharge diverges, has
  none (`Relational.Divergence.prediction_without_execution`).

**Costs.**  An additive cost is a pure executor; its value on a completed plan
charges each discharge once per citation of its obligation
(`Cost.cost_complete`).  For a plan citing each obligation exactly once this is
the cost of executing each discharge once (`Cost.cost_complete_of_linear`); a
plan citing an obligation twice pays its discharge twice
(`Cost.Controls.shared_obligation_paid_twice`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe u

variable {object : Object}

/-! ## Residuals -/

section Residuals

variable (object) (carrier : Pattern → Type u)

mutual

/-- **The residual of a partially executed plan**: values for its determined
sub-derivations, holes for its obligations, and pending rule nodes above the
holes. -/
inductive Residual (context : List Pattern) : Pattern → Type u where
  | value {goal : Pattern} (value : carrier goal) : Residual context goal
  | hole (index : Fin context.length) : Residual context (context.get index)
  | node (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern}
      (application : RuleApplication object.definition ruleInstance premises conclusion)
      (children : ResidualList context premises) : Residual context conclusion

/-- Residuals of an ordered vector of sub-plans. -/
inductive ResidualList (context : List Pattern) : List Pattern → Type u where
  | nil : ResidualList context []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : Residual context premise) (tail : ResidualList context premises) :
      ResidualList context (premise :: premises)

end

variable {object} {carrier}

/-- The values of a residual vector, when every entry is a value. -/
def ResidualList.values? {context : List Pattern} :
    {goals : List Pattern} → ResidualList object carrier context goals →
      Option (RealizationList carrier goals)
  | [], .nil => some .nil
  | _ :: _, .cons (.value value) tail => (tail.values?).map (.cons value)
  | _ :: _, .cons (.hole _) _ => none
  | _ :: _, .cons (.node _ _ _) _ => none

mutual

/-- A residual is **reduced** when no rule node has only values below it: the
determined parts have been executed. -/
inductive Reduced {context : List Pattern} :
    {goal : Pattern} → Residual object carrier context goal → Prop
  | value {goal : Pattern} (value : carrier goal) : Reduced (.value value)
  | hole (index : Fin context.length) : Reduced (.hole index)
  | node (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern}
      (application : RuleApplication object.definition ruleInstance premises conclusion)
      {children : ResidualList object carrier context premises}
      (pending : children.values? = none) (reduced : ReducedList children) :
      Reduced (.node ruleInstance application children)

/-- Pointwise reducedness. -/
inductive ReducedList {context : List Pattern} :
    {goals : List Pattern} → ResidualList object carrier context goals → Prop
  | nil : ReducedList .nil
  | cons {premise : Pattern} {premises : List Pattern}
      {head : Residual object carrier context premise}
      {tail : ResidualList object carrier context premises} :
      Reduced head → ReducedList tail → ReducedList (.cons head tail)

end

end Residuals

/-- Sum of natural-number values. -/
def valueSum : {goals : List Pattern} → RealizationList (fun _ => ℕ) goals → ℕ
  | [], .nil => 0
  | _ :: _, .cons head tail => head + valueSum tail

/-- Read an ordered vector of digits as a number: `[x, y]` is `10 * x + y`. -/
def valueDigits : {goals : List Pattern} → ℕ → RealizationList (fun _ => ℕ) goals → ℕ
  | [], accumulated, .nil => accumulated
  | _ :: _, accumulated, .cons head tail => valueDigits (10 * accumulated + head) tail

/-! ## Pure total executors -/

section Pure

variable (model : Model.{u} object)

mutual

/-- **Partial execution**: execute every sub-derivation without obligations;
keep holes and the rule nodes above them. -/
def peval {context : List Pattern} :
    {goal : Pattern} → OpenDerivation object.definition context goal →
      Residual object model.carrier context goal
  | _, .assumption index => .hole index
  | _, .byRule ruleInstance application children =>
      match (pevalList children).values? with
      | some values => .value (model.onRule ruleInstance application values)
      | none => .node ruleInstance application (pevalList children)

/-- Partial execution of an ordered vector of sub-plans. -/
def pevalList {context : List Pattern} :
    {goals : List Pattern} → OpenDerivationList object.definition context goals →
      ResidualList object model.carrier context goals
  | _, .nil => .nil
  | _, .cons head tail => .cons (peval head) (pevalList tail)

end

mutual

/-- **Resumption**: finish a residual on values for the obligations. -/
def resume {context : List Pattern} :
    {goal : Pattern} → Residual object model.carrier context goal →
      RealizationList model.carrier context → model.carrier goal
  | _, .value value, _ => value
  | _, .hole index, environment => environment.get index
  | _, .node ruleInstance application children, environment =>
      model.onRule ruleInstance application (resumeList children environment)

/-- Resumption of an ordered vector of residuals. -/
def resumeList {context : List Pattern} :
    {goals : List Pattern} → ResidualList object model.carrier context goals →
      RealizationList model.carrier context → RealizationList model.carrier goals
  | _, .nil, _ => .nil
  | _, .cons head tail, environment =>
      .cons (resume head environment) (resumeList tail environment)

end

variable {model}

/-- A vector of values resumes to itself. -/
theorem resumeList_of_values? {context : List Pattern} :
    {goals : List Pattern} → (residuals : ResidualList object model.carrier context goals) →
      {values : RealizationList model.carrier goals} →
      residuals.values? = some values →
        ∀ environment, resumeList model residuals environment = values
  | [], .nil, values, _, _ => by
      cases values
      rfl
  | _ :: _, .cons (.value value) tail, values, found, environment => by
      simp only [ResidualList.values?, Option.map_eq_some_iff] at found
      obtain ⟨tailValues, tailFound, rfl⟩ := found
      simp only [resumeList, resume]
      rw [resumeList_of_values? tail tailFound environment]
  | _ :: _, .cons (.hole _) _, _, found, _ => by simp [ResidualList.values?] at found
  | _ :: _, .cons (.node _ _ _) _, _, found, _ => by simp [ResidualList.values?] at found

variable (model)

mutual

/-- **Resuming a partial execution is executing the plan.** -/
theorem resume_peval {context : List Pattern} :
    {goal : Pattern} → (plan : OpenDerivation object.definition context goal) →
      (environment : RealizationList model.carrier context) →
        resume model (peval model plan) environment = model.denoteOpen plan environment
  | _, .assumption index, environment => rfl
  | _, .byRule ruleInstance application children, environment => by
      have childrenResume := resumeList_pevalList children environment
      simp only [peval, Model.denoteOpen]
      cases found : (pevalList model children).values? with
      | none =>
          simp only [resume]
          rw [childrenResume]
      | some values =>
          simp only [resume]
          rw [← childrenResume, resumeList_of_values? _ found environment]

/-- Pointwise form for ordered vectors. -/
theorem resumeList_pevalList {context : List Pattern} :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition context goals) →
      (environment : RealizationList model.carrier context) →
        resumeList model (pevalList model plans) environment =
          model.denoteOpenList plans environment
  | _, .nil, _ => rfl
  | _, .cons head tail, environment => by
      simp only [pevalList, resumeList, Model.denoteOpenList]
      rw [resume_peval head environment, resumeList_pevalList tail environment]

end

/-- **Fill-and-resume for plans.**  Resuming the partial execution of a plan on
the values of the derivations that discharge its obligations is executing the
completed plan. -/
theorem fill_and_resume {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) :
    resume model (peval model plan) (model.denoteList evidence) =
      model.denote (plan.discharge evidence) := by
  rw [resume_peval, Model.denote_discharge]

/-- **Incremental discharge in stages.**  Resuming a partially discharged plan
resumes the original plan on the values of the discharging sub-plans. -/
theorem staged_resume {source target : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition source goal)
    (environment : OpenDerivationList object.definition target source)
    (values : RealizationList model.carrier target) :
    resume model (peval model (plan.bind environment)) values =
      resume model (peval model plan) (model.denoteOpenList environment values) := by
  rw [resume_peval, resume_peval, Model.denoteOpen_bind]

/-- **Behaviour before discharge.**  If partial execution already produced a
value, every completion of the plan has that value. -/
theorem determinate {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal) {value : model.carrier goal}
    (executed : peval model plan = .value value)
    (evidence : DerivationList object.definition context) :
    model.denote (plan.discharge evidence) = value := by
  rw [← fill_and_resume, executed]
  rfl

mutual

/-- **Partial execution executes every determined part.** -/
theorem peval_reduced {context : List Pattern} :
    {goal : Pattern} → (plan : OpenDerivation object.definition context goal) →
      Reduced (peval model plan)
  | _, .assumption index => .hole index
  | _, .byRule ruleInstance application children => by
      simp only [peval]
      cases found : (pevalList model children).values? with
      | none => exact .node ruleInstance application found (pevalList_reduced children)
      | some values => exact .value _

/-- Pointwise form. -/
theorem pevalList_reduced {context : List Pattern} :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition context goals) →
      ReducedList (pevalList model plans)
  | _, .nil => .nil
  | _, .cons head tail => .cons (peval_reduced head) (pevalList_reduced tail)

end

end Pure

/-! ## Controls for pure executors -/

namespace PureControls

open Fixture

/-- The size executor: each rule node counts one. -/
abbrev sizeModel : Model.{0} kernel where
  carrier := fun _ => ℕ
  onRule := fun _ _ _ _ values => valueSum values + 1

/-- **Positive.**  The partial execution of `both(?A, ab(axA₁))` already
executed `ab(axA₁)`; resuming it on the size of `axA₁` gives the size of the
completed plan. -/
theorem planBoth_resume :
    resume sizeModel (peval sizeModel planBoth) (sizeModel.denoteList (.cons dA₁ .nil)) = 4 ∧
      sizeModel.denote (planBoth.discharge (.cons dA₁ .nil)) = 4 :=
  ⟨rfl, rfl⟩

/-- **Positive.**  A plan without obligations executes completely. -/
theorem closed_determinate :
    peval sizeModel (OpenDerivation.ofClosed (context := []) dC) = .value 3 := rfl

/-- **Negative.**  `bc(?B)` is not determined before discharge: its completions
`bc(axB)` and `bc(ab(axA₁))` have different sizes, so its partial execution is
not a value. -/
theorem planBC_indeterminate :
    sizeModel.denote (planBC.discharge (.cons dB .nil)) = 2 ∧
      sizeModel.denote (planBC.discharge (.cons dBA₁ .nil)) = 3 ∧
      ∀ value, peval sizeModel planBC ≠ .value value := by
  refine ⟨rfl, rfl, fun value executed => ?_⟩
  have first := determinate sizeModel planBC executed (.cons dB .nil)
  have second := determinate sizeModel planBC executed (.cons dBA₁ .nil)
  have two : sizeModel.denote (planBC.discharge (.cons dB .nil)) = 2 := rfl
  have three : sizeModel.denote (planBC.discharge (.cons dBA₁ .nil)) = 3 := rfl
  rw [two] at first
  rw [three] at second
  exact absurd (first.trans second.symm) (by decide)

end PureControls

/-! ## Relational executors: termination and nondeterminism -/

namespace Relational

/-- **A relational executor**: a step relates the values of its premises to
values of its conclusion.  A step may have no output (its procedure diverges)
or several (it is nondeterministic). -/
structure Executor (object : Object) where
  carrier : Pattern → Type u
  step : ∀ (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern},
    RuleApplication object.definition ruleInstance premises conclusion →
      RealizationList carrier premises → carrier conclusion → Prop

variable (executor : Executor.{u} object)

mutual

/-- **Execution of a plan on values for its obligations.**  Every
sub-derivation is executed, strictly. -/
def Runs {context : List Pattern} (environment : RealizationList executor.carrier context) :
    {goal : Pattern} → OpenDerivation object.definition context goal →
      executor.carrier goal → Prop
  | _, .assumption index, value => value = environment.get index
  | _, .byRule ruleInstance application children, value =>
      ∃ values, RunsList environment children values ∧
        executor.step ruleInstance application values value

/-- Execution of an ordered vector of sub-plans. -/
def RunsList {context : List Pattern} (environment : RealizationList executor.carrier context) :
    {goals : List Pattern} → OpenDerivationList object.definition context goals →
      RealizationList executor.carrier goals → Prop
  | _, .nil, values => values = .nil
  | _, .cons head tail, .cons value values =>
      Runs environment head value ∧ RunsList environment tail values

end

/-- Execution of a closed derivation. -/
def Executes {goal : Pattern} (derivation : Derivation object.definition goal)
    (value : executor.carrier goal) : Prop :=
  Runs executor .nil (OpenDerivation.ofClosed derivation) value

/-- A relational executor is deterministic when every step has at most one
output. -/
def Deterministic : Prop :=
  ∀ (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication object.definition ruleInstance premises conclusion)
    (values : RealizationList executor.carrier premises) (first second : executor.carrier conclusion),
    executor.step ruleInstance application values first →
      executor.step ruleInstance application values second → first = second

variable {executor}

theorem runsList_get {context : List Pattern}
    {environment : RealizationList executor.carrier context} :
    {goals : List Pattern} → (derivations : OpenDerivationList object.definition context goals) →
      (values : RealizationList executor.carrier goals) →
      RunsList executor environment derivations values →
        ∀ index, Runs executor environment (derivations.get index) (values.get index)
  | [], .nil, .nil, _, index => Fin.elim0 index
  | _ :: _, .cons _ tail, .cons _ values, runs, index => by
      simp only [RunsList] at runs
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact runs.1
      · exact runsList_get tail values runs.2 tailIndex

mutual

/-- **Resumption is realized when the discharges terminate.**  A value of the
plan on the values of terminating discharges is a value of the discharged
plan.  No determinism is needed. -/
theorem runs_bind {source target : List Pattern}
    {environment : RealizationList executor.carrier target}
    {substitution : OpenDerivationList object.definition target source}
    {values : RealizationList executor.carrier source}
    (discharged : RunsList executor environment substitution values) :
    {goal : Pattern} → (plan : OpenDerivation object.definition source goal) →
      (value : executor.carrier goal) →
      Runs executor values plan value → Runs executor environment (plan.bind substitution) value
  | _, .assumption index, value, runs => by
      simp only [Runs] at runs
      subst runs
      exact runsList_get substitution values discharged index
  | _, .byRule _ _ children, value, runs => by
      simp only [Runs] at runs
      obtain ⟨childValues, childrenRun, stepped⟩ := runs
      exact ⟨childValues, runsList_bind discharged children childValues childrenRun, stepped⟩

/-- Pointwise form. -/
theorem runsList_bind {source target : List Pattern}
    {environment : RealizationList executor.carrier target}
    {substitution : OpenDerivationList object.definition target source}
    {values : RealizationList executor.carrier source}
    (discharged : RunsList executor environment substitution values) :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition source goals) →
      (results : RealizationList executor.carrier goals) →
      RunsList executor values plans results →
        RunsList executor environment (plans.bind substitution) results
  | _, .nil, results, runs => runs
  | _, .cons head tail, .cons result results, runs => by
      simp only [RunsList] at runs
      exact ⟨runs_bind discharged head result runs.1,
        runsList_bind discharged tail results runs.2⟩

end

mutual

/-- Deterministic executors execute each plan to at most one value. -/
theorem runs_deterministic (deterministic : Deterministic executor)
    {context : List Pattern} {environment : RealizationList executor.carrier context} :
    {goal : Pattern} → (plan : OpenDerivation object.definition context goal) →
      (first second : executor.carrier goal) →
      Runs executor environment plan first → Runs executor environment plan second →
        first = second
  | _, .assumption _, _, _, firstRun, secondRun => by
      simp only [Runs] at firstRun secondRun
      rw [firstRun, secondRun]
  | _, .byRule ruleInstance application children, _, _, firstRun, secondRun => by
      simp only [Runs] at firstRun secondRun
      obtain ⟨firstValues, firstChildren, firstStep⟩ := firstRun
      obtain ⟨secondValues, secondChildren, secondStep⟩ := secondRun
      have same := runsList_deterministic deterministic children firstValues secondValues
        firstChildren secondChildren
      subst same
      exact deterministic ruleInstance application _ _ _ firstStep secondStep

/-- Pointwise form. -/
theorem runsList_deterministic (deterministic : Deterministic executor)
    {context : List Pattern} {environment : RealizationList executor.carrier context} :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition context goals) →
      (first second : RealizationList executor.carrier goals) →
      RunsList executor environment plans first → RunsList executor environment plans second →
        first = second
  | _, .nil, _, _, firstRun, secondRun => by
      simp only [RunsList] at firstRun secondRun
      rw [firstRun, secondRun]
  | _, .cons head tail, .cons firstHead firstTail, .cons secondHead secondTail,
      firstRun, secondRun => by
      simp only [RunsList] at firstRun secondRun
      rw [runs_deterministic deterministic head firstHead secondHead firstRun.1 secondRun.1,
        runsList_deterministic deterministic tail firstTail secondTail firstRun.2 secondRun.2]

end

mutual

/-- **For deterministic executors, every value of the discharged plan is a
resumed value.** -/
theorem runs_of_runs_bind (deterministic : Deterministic executor)
    {source target : List Pattern}
    {environment : RealizationList executor.carrier target}
    {substitution : OpenDerivationList object.definition target source}
    {values : RealizationList executor.carrier source}
    (discharged : RunsList executor environment substitution values) :
    {goal : Pattern} → (plan : OpenDerivation object.definition source goal) →
      (value : executor.carrier goal) →
      Runs executor environment (plan.bind substitution) value → Runs executor values plan value
  | _, .assumption index, value, runs =>
      runs_deterministic deterministic (substitution.get index) value (values.get index) runs
        (runsList_get substitution values discharged index)
  | _, .byRule _ _ children, value, runs => by
      simp only [OpenDerivation.bind, Runs] at runs
      obtain ⟨childValues, childrenRun, stepped⟩ := runs
      exact ⟨childValues,
        runsList_of_runsList_bind deterministic discharged children childValues childrenRun, stepped⟩

/-- Pointwise form. -/
theorem runsList_of_runsList_bind (deterministic : Deterministic executor)
    {source target : List Pattern}
    {environment : RealizationList executor.carrier target}
    {substitution : OpenDerivationList object.definition target source}
    {values : RealizationList executor.carrier source}
    (discharged : RunsList executor environment substitution values) :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition source goals) →
      (results : RealizationList executor.carrier goals) →
      RunsList executor environment (plans.bind substitution) results →
        RunsList executor values plans results
  | _, .nil, results, runs => runs
  | _, .cons head tail, .cons result results, runs => by
      simp only [OpenDerivationList.bind, RunsList] at runs
      exact ⟨runs_of_runs_bind deterministic discharged head result runs.1,
        runsList_of_runsList_bind deterministic discharged tail results runs.2⟩

end

/-- The discharged plan, read as an open derivation, is the plan bound to the
closed evidence. -/
theorem ofClosed_discharge {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) :
    OpenDerivation.ofClosed (context := []) (plan.discharge evidence) =
      plan.bind (OpenDerivationList.ofClosed evidence) := by
  unfold OpenDerivation.discharge
  exact OpenDerivation.ofClosed_close _

/-- **Resumed values are realized when the discharges terminate.** -/
theorem executes_discharge_of_runs {context : List Pattern} {goal : Pattern}
    {plan : OpenDerivation object.definition context goal}
    {evidence : DerivationList object.definition context}
    {values : RealizationList executor.carrier context}
    (discharged : RunsList executor .nil (OpenDerivationList.ofClosed evidence) values)
    {value : executor.carrier goal} (resumed : Runs executor values plan value) :
    Executes executor (plan.discharge evidence) value := by
  unfold Executes
  rw [ofClosed_discharge]
  exact runs_bind discharged plan value resumed

/-- **Fill-and-resume for deterministic partial executors.**  When the
discharges terminate, the values of the completed plan are exactly the
resumed values. -/
theorem executes_discharge_iff (deterministic : Deterministic executor)
    {context : List Pattern} {goal : Pattern}
    {plan : OpenDerivation object.definition context goal}
    {evidence : DerivationList object.definition context}
    {values : RealizationList executor.carrier context}
    (discharged : RunsList executor .nil (OpenDerivationList.ofClosed evidence) values)
    (value : executor.carrier goal) :
    Executes executor (plan.discharge evidence) value ↔ Runs executor values plan value := by
  constructor
  · intro executes
    unfold Executes at executes
    rw [ofClosed_discharge] at executes
    exact runs_of_runs_bind deterministic discharged plan value executes
  · exact executes_discharge_of_runs discharged

/-! ### Control: termination -/

namespace Divergence

open Fixture

/-- Every procedure returns `0`, except the procedure of `loop`, which never
returns. -/
abbrev divergentExecutor : Executor.{0} kernel where
  carrier := fun _ => ℕ
  step := fun ruleInstance _ _ _ _ value => ruleInstance.ruleId ≠ ruleLoop.id ∧ value = 0

/-- `weak(?L)` predicts the value `0` for every value of its obligation. -/
theorem prediction (value : ℕ) : Runs divergentExecutor (.cons value .nil) planWeak 0 :=
  ⟨.cons value .nil, ⟨rfl, rfl⟩, by decide, rfl⟩

/-- **Negative control.**  Resumption predicts `0` for `weak(?L)` whatever
discharges `L`, but discharged by the diverging `loop`, the completed plan has
no value: resumption predicts only terminating completions. -/
theorem prediction_without_execution :
    (∀ value, Runs divergentExecutor (.cons value .nil) planWeak 0) ∧
      ∀ value, ¬ Executes divergentExecutor (planWeak.discharge (.cons dL .nil)) value := by
  refine ⟨prediction, fun value executes => ?_⟩
  unfold Executes at executes
  rw [ofClosed_discharge] at executes
  obtain ⟨childValues, childrenRun, _⟩ := executes
  cases childValues with
  | cons loopValue rest =>
      obtain ⟨loopRun, _⟩ := childrenRun
      obtain ⟨_, _, stepped⟩ := loopRun
      exact stepped.1 rfl

end Divergence

/-! ### Control: nondeterminism is an effect -/

namespace Nondeterminism

open Fixture

/-- The procedure of `axA₁` returns `0` or `1`; every other procedure adds the
values of its premises. -/
abbrev nondeterministicExecutor : Executor.{0} kernel where
  carrier := fun _ => ℕ
  step := fun ruleInstance _ _ _ values value =>
    if ruleInstance.ruleId = ruleAxA₁.id then value = 0 ∨ value = 1 else value = valueSum values

/-- The completed plan `pair(axA₁, axA₁)` runs `axA₁` twice, independently, and
can produce `0 + 1`. -/
theorem completed_one :
    Executes nondeterministicExecutor (planPairShared.discharge (.cons dA₁ .nil)) 1 := by
  unfold Executes
  rw [ofClosed_discharge]
  refine ⟨.cons 0 (.cons 1 .nil), ⟨⟨.nil, rfl, ?_⟩, ⟨.nil, rfl, ?_⟩, rfl⟩, ?_⟩
  · simp [ruleInstance]
  · simp [ruleInstance]
  · simp [ruleInstance, rulePair, ruleAxA₁, groundRule, valueSum]

/-- **Negative control.**  Resumption executes the discharge of the shared
obligation once and reuses its value, so it produces only even values; the
completed plan produces `1`. -/
theorem completed_value_not_resumed :
    Executes nondeterministicExecutor (planPairShared.discharge (.cons dA₁ .nil)) 1 ∧
      ¬ ∃ values, RunsList nondeterministicExecutor .nil
          (OpenDerivationList.ofClosed (.cons dA₁ .nil)) values ∧
        Runs nondeterministicExecutor values planPairShared 1 := by
  refine ⟨completed_one, ?_⟩
  rintro ⟨values, -, resumed⟩
  cases values with
  | cons value rest =>
      cases rest
      obtain ⟨childValues, childrenRun, stepped⟩ := resumed
      cases childValues with
      | cons first tail =>
          cases tail with
          | cons second rest' =>
              cases rest'
              obtain ⟨firstRun, secondRun, -⟩ := childrenRun
              simp only [Runs] at firstRun secondRun
              subst firstRun
              subst secondRun
              simp [ruleInstance, rulePair, ruleAxA₁, groundRule, valueSum] at stepped
              omega

end Nondeterminism

end Relational

/-! ## Stateful executors: purity -/

namespace Stateful

/-- **A stateful executor**: every step reads and updates a state. -/
structure Executor (object : Object) (State : Type) where
  carrier : Pattern → Type
  act : ∀ (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern},
    RuleApplication object.definition ruleInstance premises conclusion →
      RealizationList carrier premises → State → carrier conclusion × State

variable {State : Type} (executor : Executor object State)

mutual

/-- Execute a closed derivation in plan order: premises from left to right,
then the step. -/
def run : {goal : Pattern} → Derivation object.definition goal → State →
    executor.carrier goal × State
  | _, .byRule ruleInstance application children, state =>
      let result := runList children state
      executor.act ruleInstance application result.1 result.2

/-- Execute an ordered vector of closed derivations from left to right. -/
def runList : {goals : List Pattern} → DerivationList object.definition goals → State →
    RealizationList executor.carrier goals × State
  | _, .nil, state => (.nil, state)
  | _, .cons head tail, state =>
      let first := run head state
      let rest := runList tail first.2
      (.cons first.1 rest.1, rest.2)

end

mutual

/-- Partial execution: execute every sub-derivation without obligations, in
plan order. -/
def speval {context : List Pattern} :
    {goal : Pattern} → OpenDerivation object.definition context goal → State →
      Residual object executor.carrier context goal × State
  | _, .assumption index, state => (.hole index, state)
  | _, .byRule ruleInstance application children, state =>
      let result := spevalList children state
      match result.1.values? with
      | some values =>
          let executed := executor.act ruleInstance application values result.2
          (.value executed.1, executed.2)
      | none => (.node ruleInstance application result.1, result.2)

/-- Partial execution of an ordered vector of sub-plans. -/
def spevalList {context : List Pattern} :
    {goals : List Pattern} → OpenDerivationList object.definition context goals → State →
      ResidualList object executor.carrier context goals × State
  | _, .nil, state => (.nil, state)
  | _, .cons head tail, state =>
      let first := speval head state
      let rest := spevalList tail first.2
      (.cons first.1 rest.1, rest.2)

end

mutual

/-- Resumption: finish the residual on values for the obligations. -/
def sresume {context : List Pattern} :
    {goal : Pattern} → Residual object executor.carrier context goal →
      RealizationList executor.carrier context → State → executor.carrier goal × State
  | _, .value value, _, state => (value, state)
  | _, .hole index, environment, state => (environment.get index, state)
  | _, .node ruleInstance application children, environment, state =>
      let result := sresumeList children environment state
      executor.act ruleInstance application result.1 result.2

/-- Resumption of an ordered vector of residuals. -/
def sresumeList {context : List Pattern} :
    {goals : List Pattern} → ResidualList object executor.carrier context goals →
      RealizationList executor.carrier context → State →
        RealizationList executor.carrier goals × State
  | _, .nil, _, state => (.nil, state)
  | _, .cons head tail, environment, state =>
      let first := sresume head environment state
      let rest := sresumeList tail environment first.2
      (.cons first.1 rest.1, rest.2)

end

/-- **Incremental execution**: the determined parts now, then the discharges
in obligation order, then the residual. -/
def incremental {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) (state : State) :
    executor.carrier goal × State :=
  let partialRun := speval executor plan state
  let discharged := runList executor evidence partialRun.2
  sresume executor partialRun.1 discharged.1 discharged.2

/-! ### Purity suffices -/

/-- A pure executor as a stateful one: steps neither read nor change the
state. -/
abbrev ofModel (model : Model.{0} object) (State : Type) : Executor object State where
  carrier := model.carrier
  act := fun ruleInstance _ _ application values state =>
    (model.onRule ruleInstance application values, state)

mutual

theorem run_ofModel (model : Model.{0} object) {State : Type} :
    {goal : Pattern} → (derivation : Derivation object.definition goal) → (state : State) →
      run (ofModel model State) derivation state = (model.denote derivation, state)
  | _, .byRule ruleInstance application children, state => by
      simp only [run, runList_ofModel model children state, Model.denote]

theorem runList_ofModel (model : Model.{0} object) {State : Type} :
    {goals : List Pattern} → (derivations : DerivationList object.definition goals) →
      (state : State) →
      runList (ofModel model State) derivations state = (model.denoteList derivations, state)
  | _, .nil, _ => rfl
  | _, .cons head tail, state => by
      simp only [runList, run_ofModel model head state, runList_ofModel model tail state,
        Model.denoteList]

end

mutual

theorem speval_ofModel (model : Model.{0} object) {State : Type} {context : List Pattern} :
    {goal : Pattern} → (plan : OpenDerivation object.definition context goal) →
      (state : State) → speval (ofModel model State) plan state = (peval model plan, state)
  | _, .assumption _, _ => rfl
  | _, .byRule ruleInstance application children, state => by
      simp only [speval, spevalList_ofModel model children state, peval]
      cases (pevalList model children).values? <;> rfl

theorem spevalList_ofModel (model : Model.{0} object) {State : Type} {context : List Pattern} :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition context goals) →
      (state : State) → spevalList (ofModel model State) plans state = (pevalList model plans, state)
  | _, .nil, _ => rfl
  | _, .cons head tail, state => by
      simp only [spevalList, speval_ofModel model head state,
        spevalList_ofModel model tail state, pevalList]

end

mutual

theorem sresume_ofModel (model : Model.{0} object) {State : Type} {context : List Pattern} :
    {goal : Pattern} → (residual : Residual object model.carrier context goal) →
      (environment : RealizationList model.carrier context) → (state : State) →
      sresume (ofModel model State) residual environment state =
        (resume model residual environment, state)
  | _, .value _, _, _ => rfl
  | _, .hole _, _, _ => rfl
  | _, .node ruleInstance application children, environment, state => by
      simp only [sresume, sresumeList_ofModel model children environment state, resume]

theorem sresumeList_ofModel (model : Model.{0} object) {State : Type} {context : List Pattern} :
    {goals : List Pattern} → (residuals : ResidualList object model.carrier context goals) →
      (environment : RealizationList model.carrier context) → (state : State) →
      sresumeList (ofModel model State) residuals environment state =
        (resumeList model residuals environment, state)
  | _, .nil, _, _ => rfl
  | _, .cons head tail, environment, state => by
      simp only [sresumeList, sresume_ofModel model head environment state,
        sresumeList_ofModel model tail environment state, resumeList]

end

/-- **Purity suffices**: for an executor without effects, incremental
execution is execution of the completed plan. -/
theorem incremental_ofModel (model : Model.{0} object) {State : Type}
    {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) (state : State) :
    incremental (ofModel model State) plan evidence state =
      run (ofModel model State) (plan.discharge evidence) state := by
  simp only [incremental, speval_ofModel, runList_ofModel, sresume_ofModel, run_ofModel,
    fill_and_resume]

namespace Controls

open Fixture

/-- The counter executor: `axA₁` returns the counter and increments it; every
other step reads its premise values as digits. -/
abbrev tickExecutor : Executor kernel ℕ where
  carrier := fun _ => ℕ
  act := fun ruleInstance _ _ _ values counter =>
    if ruleInstance.ruleId = ruleAxA₁.id then (counter, counter + 1)
    else (valueDigits 0 values, counter)

/-- In plan order, `both(axA₁, ab(axA₁))` reads the counter first at the
obligation. -/
theorem completed_run :
    run tickExecutor (planBoth.discharge (.cons dA₁ .nil)) 0 = (1, 2) := rfl

/-- Incremental execution runs the determined `ab(axA₁)` before the
discharge. -/
theorem incremental_run :
    incremental tickExecutor planBoth (.cons dA₁ .nil) 0 = (10, 2) := rfl

/-- **Negative control: with effects, incremental execution and execution of
the completed plan disagree.** -/
theorem commutation_fails :
    (run tickExecutor (planBoth.discharge (.cons dA₁ .nil)) 0).1 ≠
      (incremental tickExecutor planBoth (.cons dA₁ .nil) 0).1 := by
  rw [completed_run, incremental_run]
  decide

/-- **Positive control**: when the obligation is the first effect in plan order,
the two executions agree. -/
theorem obligation_first_agrees :
    run tickExecutor (planAB.discharge (.cons dA₁ .nil)) 0 =
      incremental tickExecutor planAB (.cons dA₁ .nil) 0 := rfl

end Controls

end Stateful

/-! ## Contextual executors: the recorded context -/

namespace Contextual

/-- **A contextual executor**: a step may change the context in which its
premises are executed (as a step that introduces a hypothesis does), and may
read its own context. -/
structure Executor (object : Object) where
  Context : Type
  carrier : Pattern → Type
  enter : ∀ (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern},
    RuleApplication object.definition ruleInstance premises conclusion → Context → Context
  act : ∀ (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern},
    RuleApplication object.definition ruleInstance premises conclusion → Context →
      RealizationList carrier premises → carrier conclusion

variable (executor : Executor object)

mutual

/-- Execute an open derivation; an obligation receives the context of its own
position. -/
def run {context : List Pattern}
    (holeValue : (index : Fin context.length) → executor.Context →
      executor.carrier (context.get index)) :
    {goal : Pattern} → executor.Context → OpenDerivation object.definition context goal →
      executor.carrier goal
  | _, current, .assumption index => holeValue index current
  | _, current, .byRule ruleInstance application children =>
      executor.act ruleInstance application current
        (runList holeValue (executor.enter ruleInstance application current) children)

/-- Execute an ordered vector of sub-plans in one context. -/
def runList {context : List Pattern}
    (holeValue : (index : Fin context.length) → executor.Context →
      executor.carrier (context.get index)) :
    {goals : List Pattern} → executor.Context → OpenDerivationList object.definition context goals →
      RealizationList executor.carrier goals
  | _, _, .nil => .nil
  | _, current, .cons head tail => .cons (run holeValue current head) (runList holeValue current tail)

end

/-- No obligations. -/
def noHoles : (index : Fin ([] : List Pattern).length) → executor.Context →
    executor.carrier (([] : List Pattern).get index) :=
  fun index _ => Fin.elim0 index

mutual

/-- **Substitution law**: executing a partially discharged plan resumes each
obligation in the context recorded at its position. -/
theorem run_bind {source target : List Pattern}
    (holeValue : (index : Fin target.length) → executor.Context →
      executor.carrier (target.get index))
    (substitution : OpenDerivationList object.definition target source) :
    {goal : Pattern} → (current : executor.Context) →
      (plan : OpenDerivation object.definition source goal) →
      run executor holeValue current (plan.bind substitution) =
        run executor (fun index here => run executor holeValue here (substitution.get index))
          current plan
  | _, _, .assumption _ => rfl
  | _, current, .byRule ruleInstance application children => by
      simp only [OpenDerivation.bind, run]
      rw [runList_bind holeValue substitution (executor.enter ruleInstance application current)
        children]

/-- Pointwise form. -/
theorem runList_bind {source target : List Pattern}
    (holeValue : (index : Fin target.length) → executor.Context →
      executor.carrier (target.get index))
    (substitution : OpenDerivationList object.definition target source) :
    {goals : List Pattern} → (current : executor.Context) →
      (plans : OpenDerivationList object.definition source goals) →
      runList executor holeValue current (plans.bind substitution) =
        runList executor (fun index here => run executor holeValue here (substitution.get index))
          current plans
  | _, _, .nil => rfl
  | _, current, .cons head tail => by
      simp only [OpenDerivationList.bind, runList]
      rw [run_bind holeValue substitution current head,
        runList_bind holeValue substitution current tail]

end

/-- Resume every obligation by executing its discharge in the context recorded
at the obligation's position. -/
def recordedHoles {context : List Pattern} (evidence : DerivationList object.definition context) :
    (index : Fin context.length) → executor.Context → executor.carrier (context.get index) :=
  fun index here =>
    run executor (noHoles executor) here ((OpenDerivationList.ofClosed evidence).get index)

/-- Resume every obligation by executing its discharge in one fixed context,
ignoring the recorded one. -/
def topLevelHoles {context : List Pattern} (evidence : DerivationList object.definition context)
    (top : executor.Context) :
    (index : Fin context.length) → executor.Context → executor.carrier (context.get index) :=
  fun index _ =>
    run executor (noHoles executor) top ((OpenDerivationList.ofClosed evidence).get index)

/-- **Resumption in the recorded context agrees with executing the completed
plan.** -/
theorem resume_recorded {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) (current : executor.Context) :
    run executor (recordedHoles executor evidence) current plan =
      run executor (noHoles executor) current
        (OpenDerivation.ofClosed (plan.discharge evidence)) := by
  rw [Relational.ofClosed_discharge, run_bind]
  rfl

namespace Controls

open Fixture

/-- The hypothesis executor: the step `ab` introduces a hypothesis (the
context counts hypotheses), and the axiom `axA₁` reads the number of
hypotheses in scope; every other step adds its premise values. -/
abbrev hypothesisExecutor : Executor kernel where
  Context := ℕ
  carrier := fun _ => ℕ
  enter := fun ruleInstance _ _ _ current =>
    if ruleInstance.ruleId = ruleAB.id then current + 1 else current
  act := fun ruleInstance _ _ _ current values =>
    if ruleInstance.ruleId = ruleAxA₁.id then current else valueSum values

/-- **Negative control.**  The obligation of `ab(?A)` lies below the
hypothesis introduced by `ab`.  Executed in that recorded context, its
discharge `axA₁` gives `1`, as in the completed plan; executed in the context
of the whole plan, it gives `0`. -/
theorem topLevel_resumption_differs :
    run hypothesisExecutor (noHoles _) 0
        (OpenDerivation.ofClosed (planAB.discharge (.cons dA₁ .nil))) = 1 ∧
      run hypothesisExecutor (recordedHoles _ (.cons dA₁ .nil)) 0 planAB = 1 ∧
      run hypothesisExecutor (topLevelHoles _ (.cons dA₁ .nil) 0) 0 planAB = 0 :=
  ⟨rfl, rfl, rfl⟩

end Controls

end Contextual

/-! ## Costs: the commutative effect -/

namespace Cost

/-- Evaluating an ordered vector built pointwise. -/
theorem realization_get_ofFn {carrier : Pattern → Type u} :
    {goals : List Pattern} → (values : (index : Fin goals.length) → carrier (goals.get index)) →
      (index : Fin goals.length) → (RealizationList.ofFn goals values).get index = values index
  | [], _, index => Fin.elim0 index
  | _ :: _, values, index => by
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact realization_get_ofFn (fun index => values index.succ) tailIndex

/-- The additive cost executor: each rule application charges its rule. -/
abbrev costModel (charge : RuleInstance → ℕ) : Model.{0} object where
  carrier := fun _ => ℕ
  onRule := fun ruleInstance _ _ _ values => charge ruleInstance + valueSum values

/-- Zero values for every obligation. -/
def zeros (goals : List Pattern) : RealizationList (fun _ => ℕ) goals :=
  RealizationList.ofFn goals fun _ => 0

open OpenSearchMachine in
mutual

/-- **Costs are affine in the obligations**, with one term per citation. -/
theorem cost_open (charge : RuleInstance → ℕ) {context : List Pattern} :
    {goal : Pattern} → (plan : OpenDerivation object.definition context goal) →
      (values : RealizationList (fun _ => ℕ) context) →
      (costModel (object := object) charge).denoteOpen plan values =
        (costModel charge).denoteOpen plan (zeros context) +
          ((holeOccurrences plan).map fun index => values.get index).sum
  | _, .assumption index, values => by
      simp only [Model.denoteOpen, holeOccurrences, zeros, realization_get_ofFn,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | _, .byRule ruleInstance application children, values => by
      simp only [Model.denoteOpen, holeOccurrences]
      rw [costList_open charge children values]
      omega

/-- Pointwise form. -/
theorem costList_open (charge : RuleInstance → ℕ) {context : List Pattern} :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition context goals) →
      (values : RealizationList (fun _ => ℕ) context) →
      valueSum ((costModel (object := object) charge).denoteOpenList plans values) =
        valueSum ((costModel charge).denoteOpenList plans (zeros context)) +
          ((holeOccurrencesList plans).map fun index => values.get index).sum
  | _, .nil, _ => rfl
  | _, .cons head tail, values => by
      simp only [Model.denoteOpenList, valueSum, holeOccurrencesList, List.map_append,
        List.sum_append]
      rw [cost_open charge head values, costList_open charge tail values]
      omega

end

open OpenSearchMachine in
/-- **The cost of a completed plan** charges each discharge once per citation
of its obligation. -/
theorem cost_complete (charge : RuleInstance → ℕ) {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) :
    (costModel (object := object) charge).denote (plan.discharge evidence) =
      (costModel charge).denoteOpen plan (zeros context) +
        ((holeOccurrences plan).map fun index =>
          ((costModel charge).denoteList evidence).get index).sum := by
  rw [Model.denote_discharge, cost_open]

/-- Summing a vector through all its positions. -/
theorem sum_finRange_get :
    {goals : List Pattern} → (values : RealizationList (fun _ => ℕ) goals) →
      ((List.finRange goals.length).map fun index => values.get index).sum = valueSum values
  | [], .nil => rfl
  | _ :: rest, .cons head tail => by
      change ((List.finRange (rest.length + 1)).map
        fun index => (RealizationList.cons head tail).get index).sum = head + valueSum tail
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
      exact congrArg (head + ·) (sum_finRange_get tail)

open OpenSearchMachine in
/-- **For plans citing each obligation exactly once, the completed plan costs
the plan plus each discharge once**: the cost of incremental execution. -/
theorem cost_complete_of_linear (charge : RuleInstance → ℕ) {context : List Pattern}
    {goal : Pattern} (plan : OpenDerivation object.definition context goal)
    (linear : holeOccurrences plan = List.finRange context.length)
    (evidence : DerivationList object.definition context) :
    (costModel (object := object) charge).denote (plan.discharge evidence) =
      (costModel charge).denoteOpen plan (zeros context) +
        valueSum ((costModel charge).denoteList evidence) := by
  rw [cost_complete, linear, sum_finRange_get]

namespace Controls

open Fixture
open OpenSearchMachine

/-- Every rule costs one. -/
def unitCharge : RuleInstance → ℕ := fun _ => 1

/-- `pair(?A₀, ?A₁)` cites each obligation once. -/
theorem planPair_linear : holeOccurrences planPair = List.finRange 2 := rfl

/-- **Positive.**  The linear plan `pair(?A₀, ?A₁)` completed by `axA₁, axA₂`
costs the plan plus each discharge once. -/
theorem linear_cost :
    (costModel (object := kernel) unitCharge).denote
        (planPair.discharge (.cons dA₁ (.cons dA₂ .nil))) = 3 ∧
      (costModel (object := kernel) unitCharge).denoteOpen planPair (zeros _) +
        valueSum ((costModel unitCharge).denoteList (.cons dA₁ (.cons dA₂ .nil))) = 3 :=
  ⟨rfl, rfl⟩

/-- **Negative control.**  `pair(?A, ?A)` cites its obligation twice: the
completed plan pays the discharge twice, while executing each discharge once
costs one less. -/
theorem shared_obligation_paid_twice :
    holeOccurrences planPairShared = [⟨0, by decide⟩, ⟨0, by decide⟩] ∧
      (costModel (object := kernel) unitCharge).denote
          (planPairShared.discharge (.cons dA₁ .nil)) = 3 ∧
      (costModel (object := kernel) unitCharge).denoteOpen planPairShared (zeros _) +
          valueSum ((costModel unitCharge).denoteList (.cons dA₁ .nil)) = 2 :=
  ⟨rfl, rfl, rfl⟩

end Controls

end Cost

end Mettapedia.GSLT.ProofPlans
