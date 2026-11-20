import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerGrounding

/-!
# Canonical native children of the actual scanner jobs

The child view follows the existing finite scanner job list. It preserves
native scopes at binders and rejects scalar fields as recursive children.
Normality of the complete child list is exactly the native constructor's
child-normality condition. Prefix laws describe partial completion of that
same list; they do not execute the scanner or supply a normality oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalChildViews

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalScannerGrounding (kind values childJobs)

abbrev Child := Sigma fun n : Nat => Tower.Tm n
abbrev Job := Fin 5 × Fin 3

def child : {n : Nat} → Tower.Tm n → Fin 3 → Option Child
  | _, .var _, _ | _, .const _, _ | _, .head _, _ => none
  | n, .pi domain body, index | n, .sigma domain body, index =>
      if index = 0 then some ⟨n, domain⟩
      else if index = 1 then some ⟨n + 1, body⟩ else none
  | n, .id carrier left right, index =>
      if index = 0 then some ⟨n, carrier⟩
      else if index = 1 then some ⟨n, left⟩ else some ⟨n, right⟩
  | n, .lam body, index => if index = 0 then some ⟨n + 1, body⟩ else none
  | n, .app first second, index | n, .pair first second, index =>
      if index = 0 then some ⟨n, first⟩
      else if index = 1 then some ⟨n, second⟩ else none
  | n, .fst subject, index | n, .snd subject, index | n, .refl subject, index =>
      if index = 0 then some ⟨n, subject⟩ else none

theorem child_value {n : Nat} (term : Tower.Tm n) (field : Fin 3) (selected : Child)
    (found : child term field = some selected) : values term field = encodeTm selected.2 := by
  cases term <;> fin_cases field <;> simp [child] at found
  all_goals subst selected; rfl

theorem child_of_job {n : Nat} (term : Tower.Tm n) (job : Job)
    (inside : job ∈ childJobs (kind term)) :
    ∃ selected : Child, child term job.2 = some selected := by
  cases term <;>
    simp only [kind, childJobs, List.mem_cons, List.not_mem_nil, or_false] at inside
  all_goals first
    | contradiction
    | rcases inside with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem child_of_job_encoded {n : Nat} (term : Tower.Tm n) (job : Job)
    (inside : job ∈ childJobs (kind term)) :
    ∃ selected : Child, child term job.2 = some selected ∧
      values term job.2 = encodeTm selected.2 := by
  obtain ⟨selected, found⟩ := child_of_job term job inside
  exact ⟨selected, found, child_value term job.2 selected found⟩

variable {dev : Definitions.Development} (built : Compiled dev)

def JobNormal {n : Nat} (term : Tower.Tm n) (job : Job) : Prop :=
  ∃ selected : Child, child term job.2 = some selected ∧ NormalStructure.Normal built selected.2

def JobsNormal {n : Nat} (term : Tower.Tm n) (jobs : List Job) : Prop :=
  ∀ job ∈ jobs, JobNormal built term job

theorem jobNormal_iff_of_child {n : Nat} (term : Tower.Tm n) (job : Job) (selected : Child)
    (found : child term job.2 = some selected) :
    JobNormal built term job ↔ NormalStructure.Normal built selected.2 := by
  constructor
  · rintro ⟨actual, actualFound, normal⟩
    have same : selected = actual := Option.some.inj (found.symm.trans actualFound)
    cases same
    exact normal
  · intro normal
    exact ⟨selected, found, normal⟩

theorem some_child_normal (selected : Child) :
    (∃ actual : Child, (some selected : Option Child) = some actual ∧
      NormalStructure.Normal built actual.2) ↔ NormalStructure.Normal built selected.2 := by
  constructor
  · rintro ⟨actual, found, normal⟩
    have same : selected = actual := Option.some.inj found
    cases same
    exact normal
  · intro normal
    exact ⟨selected, rfl, normal⟩

@[simp] theorem jobsNormal_nil {n : Nat} (term : Tower.Tm n) : JobsNormal built term [] := by
  intro job inside
  cases inside

@[simp] theorem jobsNormal_cons {n : Nat} (term : Tower.Tm n) (job : Job) (jobs : List Job) :
    JobsNormal built term (job :: jobs) ↔ JobNormal built term job ∧ JobsNormal built term jobs := by
  simp only [JobsNormal, List.mem_cons, forall_eq_or_imp]

@[simp] theorem jobsNormal_append {n : Nat} (term : Tower.Tm n) (first second : List Job) :
    JobsNormal built term (first ++ second) ↔
      JobsNormal built term first ∧ JobsNormal built term second := by
  simp only [JobsNormal, List.mem_append, or_imp, forall_and]

theorem jobsNormal_snoc {n : Nat} (term : Tower.Tm n) (doneJobs : List Job) (job : Job) :
    JobsNormal built term (doneJobs ++ [job]) ↔
      JobsNormal built term doneJobs ∧ JobNormal built term job := by
  simp only [jobsNormal_append, jobsNormal_cons, jobsNormal_nil, and_true]

theorem jobsNormal_mono {n : Nat} (term : Tower.Tm n) {first second : List Job}
    (subset : ∀ job ∈ first, job ∈ second) (normal : JobsNormal built term second) :
    JobsNormal built term first := fun job member => normal job (subset job member)

theorem jobsNormal_take {n : Nat} (term : Tower.Tm n) (jobs : List Job) (count : Nat)
    (normal : JobsNormal built term jobs) : JobsNormal built term (jobs.take count) :=
  jobsNormal_mono built term (fun _ member => List.mem_of_mem_take member) normal

theorem jobsNormal_drop {n : Nat} (term : Tower.Tm n) (jobs : List Job) (count : Nat)
    (normal : JobsNormal built term jobs) : JobsNormal built term (jobs.drop count) :=
  jobsNormal_mono built term (fun _ member => List.mem_of_mem_drop member) normal

theorem advance_prefix {n : Nat} (term : Tower.Tm n) (doneJobs : List Job) (job : Job)
    (checked : JobsNormal built term doneJobs) (current : JobNormal built term job) :
    JobsNormal built term (doneJobs ++ [job]) :=
  (jobsNormal_snoc built term doneJobs job).mpr ⟨checked, current⟩

theorem childrenNormal_iff_jobs {n : Nat} (term : Tower.Tm n) :
    NormalStructure.ChildrenNormal built term ↔ JobsNormal built term (childJobs (kind term)) := by
  cases term <;>
    simp only [NormalStructure.ChildrenNormal, kind, childJobs,
      jobsNormal_cons, jobsNormal_nil, and_true]
  all_goals
    dsimp [JobNormal, child]
    simp only [some_child_normal]

theorem childrenNormal_of_partition {n : Nat} (term : Tower.Tm n) (doneJobs todoJobs : List Job)
    (partition : childJobs (kind term) = doneJobs ++ todoJobs)
    (checked : JobsNormal built term doneJobs) (remaining : JobsNormal built term todoJobs) :
    NormalStructure.ChildrenNormal built term := by
  apply (childrenNormal_iff_jobs built term).mpr
  rw [partition]
  exact (jobsNormal_append built term doneJobs todoJobs).mpr ⟨checked, remaining⟩

theorem failed_child_rejects {n : Nat} (term : Tower.Tm n) (job : Job)
    (inside : job ∈ childJobs (kind term)) (selected : Child)
    (found : child term job.2 = some selected)
    (failed : ¬ NormalStructure.Normal built selected.2) :
    ¬ NormalStructure.ChildrenNormal built term := by
  intro normal
  exact failed ((jobNormal_iff_of_child built term job selected found).mp
    (((childrenNormal_iff_jobs built term).mp normal) job inside))

section Controls

theorem pi_codomain_child {n : Nat} (domain : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    child (.pi domain body) 1 = some ⟨n + 1, body⟩ := rfl

theorem sigma_codomain_child {n : Nat} (domain : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    child (.sigma domain body) 1 = some ⟨n + 1, body⟩ := rfl

theorem lambda_body_child {n : Nat} (body : Tower.Tm (n + 1)) :
    child (.lam body) 0 = some ⟨n + 1, body⟩ := rfl

theorem id_third_child {n : Nat} (carrier left right : Tower.Tm n) :
    child (.id carrier left right) 2 = some ⟨n, right⟩ := rfl

theorem scalar_variable_not_child {n : Nat} (index : Fin n) (field : Fin 3) :
    child (.var index : Tower.Tm n) field = none := rfl

theorem scalar_constant_not_child {n : Nat} (name : DeclName) (field : Fin 3) :
    child (.const name : Tower.Tm n) field = none := rfl

theorem scalar_head_not_child {n : Nat} (head : Tower.Head) (field : Fin 3) :
    child (.head head : Tower.Tm n) field = none := rfl

theorem scalar_job_rejected {n : Nat} (head : Tower.Head) :
    ¬ JobsNormal built (.head head : Tower.Tm n) [(2, 0)] := by
  simp [JobsNormal, JobNormal, child]

theorem third_id_job_required {n : Nat} (carrier left right : Tower.Tm n) :
    (4, 2) ∈ childJobs (kind (.id carrier left right)) := by simp [kind, childJobs]

theorem application_has_no_third_child {n : Nat} (function argument : Tower.Tm n) :
    child (.app function argument) 2 = none := rfl

theorem equal_payload_does_not_identify_scope :
    encodeTm (.var (0 : Fin 1)) = encodeTm (.var (0 : Fin 2)) ∧
      (⟨1, .var 0⟩ : Child) ≠ ⟨2, .var 0⟩ := by
  constructor
  · rfl
  · intro same
    have arities := congrArg Sigma.fst same
    change 1 = 2 at arities
    omega

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalChildViews

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalChildViews.child_of_job_encoded
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalChildViews.childrenNormal_iff_jobs
