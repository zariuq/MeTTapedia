import Mettapedia.GSLT.LanguageDef.MultiSortedClone
import Mettapedia.OSLF.Programs.Completion

/-!
# Proof plans as partial derivations

A proof plan is a derivation with holes, and its holes are its obligations.
In a multisorted clone (`MultiSortedClone`), whose operations are derivations
from an ordered context of premise occurrences, a proof plan for a goal is an
operation into the goal whose context lists the obligations (`Plan`).  No new
carrier is introduced: for a validated proof definition the clone is
`derivationClone`, whose operations are `OpenDerivation`s.

**Completion space.**  A closed derivation completes a plan when discharging
every obligation with a closed derivation produces it (`Completes`).  This is a
satisfaction relation between complete and partial derivations, so the
completion-space theory of partial programs applies unchanged:
`completions` is the model class of a plan, refinement is entailment and
consistency is having a common completion.

**Refinement.**  Discharging obligations by sub-plans (`Plan.refine`) refines
the completion space (`refine_refines`), by associativity of substitution.
Being a syntactic instance of a plan (`InstanceOf`, the generalization order of
anti-unification) implies refinement (`InstanceOf.refines`).

**Extremes.**  The plan that assumes its own goal (`Plan.assume`) is the most
general plan: every plan for the goal is an instance of it
(`instanceOf_assume`) and every closed derivation completes it
(`mem_completions_assume`).  A plan without obligations has exactly one
completion, its own derivation (`mem_completions_closed_iff`).  A plan has a
completion exactly when every obligation is derivable
(`completions_nonempty_iff`).

**Execution.**  A clone algebra (`Algebra`) executes operations on values for
their obligations.  Its substitution law is fill-and-resume: executing a
completed plan is executing the plan on the values of the discharging
derivations (`Algebra.run_complete`), and executing a partially discharged
plan resumes the original one (`Algebra.act_refine`).  A plan whose value does
not depend on the values of its obligations determines the value of each of
its completions (`Algebra.determinate`).

**Soundness.**  A truth assignment preserved by every operation (`Truth`)
holds of the goal of every plan whose obligations hold (`Truth.plan_sound`),
and of every closed derivation.  A plan with an obligation that such an
assignment refutes has no completion (`Truth.completions_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Logic.TheoryModel
open Mettapedia.OSLF.Programs

universe u v w

variable {S : Type u} (C : MultiSortedClone.{u, v} S)

/-- **A proof plan** for `goal`: the ordered obligations and an operation of the
clone deriving the goal from them. -/
structure Plan (goal : S) : Type (max u v) where
  /-- The obligations still to be established, in order. -/
  obligations : List S
  /-- The derivation of the goal from the obligations. -/
  body : C.Hom obligations goal

/-- The empty family of values, for operations without premises. -/
def noPremises {F : S → Sort w} : (index : Fin ([] : List S).length) → F (([] : List S).get index) :=
  fun index => Fin.elim0 index

/-- A single closed derivation as evidence for the one-obligation context. -/
def singleEvidence {goal : S} (derivation : C.Hom [] goal) :
    C.Environment [] [goal] :=
  fun index => Fin.cases (motive := fun index => C.Hom [] ([goal].get index))
    derivation (fun impossible => Fin.elim0 impossible) index

/-! ## Completion spaces -/

/-- `derivation` **completes** `plan`: discharging every obligation with a
closed derivation produces it. -/
def Completes {goal : S} (derivation : C.Hom [] goal) (plan : Plan C goal) : Prop :=
  ∃ evidence : C.Environment [] plan.obligations, C.substitute plan.body evidence = derivation

/-- **The completion space** of a plan: the model class of `{plan}` under the
completion relation. -/
def completions {goal : S} (plan : Plan C goal) : Set (C.Hom [] goal) :=
  Completion.completionSpace (Completes C) plan

variable {C}

theorem mem_completions_iff {goal : S} {plan : Plan C goal} {derivation : C.Hom [] goal} :
    derivation ∈ completions C plan ↔
      ∃ evidence : C.Environment [] plan.obligations,
        C.substitute plan.body evidence = derivation :=
  Completion.mem_completionSpace (Completes C)

/-- Discharging the obligations produces a completion. -/
theorem substitute_mem_completions {goal : S} (plan : Plan C goal)
    (evidence : C.Environment [] plan.obligations) :
    C.substitute plan.body evidence ∈ completions C plan :=
  mem_completions_iff.mpr ⟨evidence, rfl⟩

/-- **A plan has a completion exactly when every obligation is derivable.** -/
theorem completions_nonempty_iff {goal : S} (plan : Plan C goal) :
    (completions C plan).Nonempty ↔ Nonempty (C.Environment [] plan.obligations) := by
  constructor
  · rintro ⟨derivation, member⟩
    obtain ⟨evidence, _⟩ := mem_completions_iff.mp member
    exact ⟨evidence⟩
  · rintro ⟨evidence⟩
    exact ⟨_, substitute_mem_completions plan evidence⟩

/-! ## Refinement -/

/-- Discharge the obligations of a plan by sub-plans over a new obligation
context. -/
def Plan.refine {goal : S} (plan : Plan C goal) {context : List S}
    (environment : C.Environment context plan.obligations) : Plan C goal :=
  ⟨context, C.substitute plan.body environment⟩

/-- **Discharging obligations refines the completion space.** -/
theorem refine_refines {goal : S} (plan : Plan C goal) {context : List S}
    (environment : C.Environment context plan.obligations) :
    Completion.Refines (Completes C) (plan.refine environment) plan := by
  intro derivation member
  obtain ⟨evidence, rfl⟩ := mem_completions_iff.mp member
  exact mem_completions_iff.mpr
    ⟨fun index => C.substitute (environment index) evidence,
      (C.substitute_assoc plan.body environment evidence).symm⟩

/-- **The generalization order**: `specific` is an instance of `general` when
it is obtained from `general` by substituting sub-plans for its obligations. -/
def InstanceOf {goal : S} (specific general : Plan C goal) : Prop :=
  ∃ environment : C.Environment specific.obligations general.obligations,
    specific.body = C.substitute general.body environment

/-- **An instance refines its generalization**: the completion space of a
generalization contains the completion space of each of its instances. -/
theorem InstanceOf.refines {goal : S} {specific general : Plan C goal}
    (instance' : InstanceOf specific general) :
    Completion.Refines (Completes C) specific general := by
  obtain ⟨environment, equation⟩ := instance'
  intro derivation member
  obtain ⟨evidence, rfl⟩ := mem_completions_iff.mp member
  refine mem_completions_iff.mpr
    ⟨fun index => C.substitute (environment index) evidence, ?_⟩
  rw [equation]
  exact (C.substitute_assoc general.body environment evidence).symm

theorem InstanceOf.refl {goal : S} (plan : Plan C goal) : InstanceOf plan plan :=
  ⟨fun index => C.project index, (C.substitute_projects plan.body).symm⟩

theorem InstanceOf.trans {goal : S} {first second third : Plan C goal}
    (firstSecond : InstanceOf first second) (secondThird : InstanceOf second third) :
    InstanceOf first third := by
  obtain ⟨environment, equation⟩ := firstSecond
  obtain ⟨environment', equation'⟩ := secondThird
  refine ⟨fun index => C.substitute (environment' index) environment, ?_⟩
  rw [equation, equation']
  exact C.substitute_assoc third.body environment' environment

/-- A plan refined by an environment is an instance of the original plan. -/
theorem refine_instanceOf {goal : S} (plan : Plan C goal) {context : List S}
    (environment : C.Environment context plan.obligations) :
    InstanceOf (plan.refine environment) plan :=
  ⟨environment, rfl⟩

/-! ## The most general plan and the closed plans -/

variable (C) in
/-- **The most general plan** for `goal`: assume the goal itself. -/
def Plan.assume (goal : S) : Plan C goal :=
  ⟨[goal], C.project (context := [goal]) ⟨0, Nat.succ_pos 0⟩⟩

/-- Every closed derivation completes the plan that assumes its goal. -/
theorem mem_completions_assume {goal : S} (derivation : C.Hom [] goal) :
    derivation ∈ completions C (Plan.assume C goal) :=
  mem_completions_iff.mpr
    ⟨singleEvidence C derivation, C.substitute_project (singleEvidence C derivation) _⟩

/-- The environment sending the assumed goal to a plan's body. -/
def assumeEnvironment {goal : S} (plan : Plan C goal) :
    C.Environment plan.obligations [goal] :=
  fun index => Fin.cases (motive := fun index => C.Hom plan.obligations ([goal].get index))
    plan.body (fun impossible => Fin.elim0 impossible) index

/-- **Every plan is an instance of the plan that assumes its goal.** -/
theorem instanceOf_assume {goal : S} (plan : Plan C goal) :
    InstanceOf plan (Plan.assume C goal) := by
  refine ⟨assumeEnvironment plan, ?_⟩
  have projected := C.substitute_project (assumeEnvironment plan)
    (⟨0, Nat.zero_lt_one⟩ : Fin [goal].length)
  exact projected.symm

variable (C) in
/-- A closed derivation, read as a plan without obligations. -/
def Plan.closed {goal : S} (derivation : C.Hom [] goal) : Plan C goal :=
  ⟨[], derivation⟩

/-- Every environment for the empty context is the identity environment. -/
theorem environment_nil_eq {context : List S} (environment : C.Environment context []) :
    environment = fun index => Fin.elim0 index :=
  funext fun index => Fin.elim0 index

/-- **A closed plan has exactly one completion: its own derivation.** -/
theorem mem_completions_closed_iff {goal : S} (derivation other : C.Hom [] goal) :
    other ∈ completions C (Plan.closed C derivation) ↔ other = derivation := by
  have projects : (fun index : Fin ([] : List S).length => C.project index) =
      fun index => Fin.elim0 index := environment_nil_eq _
  constructor
  · intro member
    obtain ⟨evidence, equation⟩ := mem_completions_iff.mp member
    rw [← equation, environment_nil_eq evidence, ← projects]
    exact C.substitute_projects derivation
  · rintro rfl
    refine mem_completions_iff.mpr ⟨fun index => C.project index, ?_⟩
    exact C.substitute_projects other

/-! ## Execution: clone algebras -/

variable (C) in
/-- **A clone algebra** executes derivations: each operation acts on values
for its premise occurrences.  Projections read their occurrence and
substitution is composition of actions. -/
structure Algebra where
  /-- The values of each sort. -/
  carrier : S → Type w
  /-- The action of an operation on values for its context. -/
  act : {context : List S} → {goal : S} → C.Hom context goal →
    ((index : Fin context.length) → carrier (context.get index)) → carrier goal
  act_project : ∀ {context : List S} (index : Fin context.length)
    (values : (index : Fin context.length) → carrier (context.get index)),
    act (C.project index) values = values index
  act_substitute : ∀ {source target : List S} {goal : S}
    (operation : C.Hom source goal) (environment : C.Environment target source)
    (values : (index : Fin target.length) → carrier (target.get index)),
    act (C.substitute operation environment) values =
      act operation (fun index => act (environment index) values)

namespace Algebra

variable (algebra : Algebra.{u, v, w} C)

/-- Execute a closed derivation. -/
def run {goal : S} (derivation : C.Hom [] goal) : algebra.carrier goal :=
  algebra.act derivation noPremises

/-- **Fill-and-resume for plans.**  Executing a completed plan is executing the
plan on the values of the derivations that discharge its obligations. -/
theorem run_complete {goal : S} (plan : Plan C goal)
    (evidence : C.Environment [] plan.obligations) :
    algebra.run (C.substitute plan.body evidence) =
      algebra.act plan.body (fun index => algebra.run (evidence index)) :=
  algebra.act_substitute plan.body evidence noPremises

/-- **Incremental discharge.**  Executing a partially discharged plan resumes
the original plan on the values of the discharging sub-plans. -/
theorem act_refine {goal : S} (plan : Plan C goal) {context : List S}
    (environment : C.Environment context plan.obligations)
    (values : (index : Fin context.length) → algebra.carrier (context.get index)) :
    algebra.act (plan.refine environment).body values =
      algebra.act plan.body (fun index => algebra.act (environment index) values) :=
  algebra.act_substitute plan.body environment values

/-- **Behaviour before discharge.**  If a plan's value does not depend on the
values of its obligations, every completion has that value. -/
theorem determinate {goal : S} (plan : Plan C goal) (value : algebra.carrier goal)
    (constant : ∀ values, algebra.act plan.body values = value) :
    ∀ derivation ∈ completions C plan, algebra.run derivation = value := by
  intro derivation member
  obtain ⟨evidence, rfl⟩ := mem_completions_iff.mp member
  rw [run_complete]
  exact constant _

end Algebra

/-! ## Soundness: truth assignments -/

variable (C) in
/-- **A truth assignment preserved by every operation.** -/
structure Truth where
  /-- Which sorts hold. -/
  holds : S → Prop
  /-- Every operation preserves truth from its context to its goal. -/
  sound : ∀ {context : List S} {goal : S}, C.Hom context goal →
    (∀ index : Fin context.length, holds (context.get index)) → holds goal

namespace Truth

variable (truth : Truth C)

/-- **Plan soundness**: the goal of a plan holds whenever its obligations
hold. -/
theorem plan_sound {goal : S} (plan : Plan C goal)
    (obligationsHold : ∀ index, truth.holds (plan.obligations.get index)) :
    truth.holds goal :=
  truth.sound plan.body obligationsHold

/-- Every closed derivation establishes a true goal. -/
theorem closed_sound {goal : S} (derivation : C.Hom [] goal) : truth.holds goal :=
  truth.sound derivation fun index => Fin.elim0 index

/-- **A refuted obligation leaves no completion.** -/
theorem completions_empty {goal : S} (plan : Plan C goal)
    (index : Fin plan.obligations.length)
    (refuted : ¬ truth.holds (plan.obligations.get index)) :
    ∀ derivation, derivation ∉ completions C plan := by
  intro derivation member
  obtain ⟨evidence, _⟩ := mem_completions_iff.mp member
  exact refuted (truth.closed_sound (evidence index))

end Truth

end Mettapedia.GSLT.ProofPlans
