import Mettapedia.Logic.WorldModel.DistributionalSpace
import Mettapedia.Logic.WorldModel.GSLTRealization
import Mettapedia.Logic.WorldModel.Observation
import Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable

/-!
# An exact table machine for distributional queries

The machine retains its source ledger and performs one variable elimination
per transition, on numerator and denominator tables. Only the final transition
normalizes. A running state is distinct from a completed impossible query.
The arithmetic is rational; the interpretation into real-valued probability
is a separate theorem. A context is an immutable model snapshot.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.WorldModel.DistributionalSpaceExecution
open Finset Mettapedia.GSLT
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable
open Mettapedia.Logic.WorldModel.GSLTRealization

variable {n : ℕ} {Id : Type} [DecidableEq Id]
variable (domains : Fin n → ℕ) (positive : ∀ v, 0 < domains v)

structure Context (Id : Type) (domains : Fin n → ℕ) where
  tables : List (Table domains)
  catalogue : Id → Constraint domains
  order : List (Fin n)
  covers : ∀ v, v ∈ order

namespace Context
variable (c : Context Id domains)

noncomputable def evidence (E : Finset Id) : List (Constraint domains) := E.toList.map c.catalogue

def mass (constraints : List (Constraint domains)) : ℚ :=
  ∑ x : Config domains, if satisfies domains constraints x then
    (combineAll domains positive c.tables).value domains positive x else 0

noncomputable def answer (E : Finset Id) (query : List (Constraint domains)) : Option ℚ :=
  let z := c.mass domains positive (c.evidence domains E)
  if 0 < z then some (c.mass domains positive (c.evidence domains E ++ query) / z) else none

@[instance_reducible] noncomputable def model : WorldModel (Finset Id) (List (Constraint domains)) (Option ℚ) where
  revise := (· ∪ ·)
  empty := ∅
  extract := c.answer domains positive

/-- The backend is the existing exact factor-table implementation. -/
def evaluate (log : List Id) (query : List (Constraint domains)) : Option ℚ :=
  conditionalQuery domains positive c.tables (log.eraseDups.map c.catalogue) query c.order

theorem evaluate_correct (log : List Id) (query : List (Constraint domains)) :
    c.evaluate domains positive log query = c.answer domains positive log.toFinset query := by
  rw [evaluate, conditionalQuery_correct domains positive _ _ _ _ c.covers]
  have he (x : Config domains) : satisfies domains (log.eraseDups.map c.catalogue) x ↔
      satisfies domains (c.evidence domains log.toFinset) x :=
    satisfies_finset domains _ _ (by ext a; simp [evidence]) x
  simp only [answer, mass, satisfies_append, he]



@[instance_reducible] noncomputable def realization :
    letI := c.model domains positive
    Realization (Finset Id) (List Id) (List (Constraint domains)) (Option ℚ) := by
  letI := c.model domains positive
  exact {
    denote := List.toFinset
    empty := []
    revise := (· ++ ·)
    extract := c.evaluate domains positive
    empty_sound := rfl
    revise_sound _ _ := List.toFinset_append
    extract_sound := c.evaluate_correct domains positive }

open Mettapedia.InformationTheory Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Logic.DistributionalSpace

/-- Nonnegative normalized rational table weights give a real-valued prior. -/
noncomputable def prior
    (nonneg : ∀ x, 0 ≤ (combineAll domains positive c.tables).value domains positive x)
    (normalized : ∑ x : Config domains,
      (combineAll domains positive c.tables).value domains positive x = 1) : Prob (Config domains) :=
  ⟨fun x => ((combineAll domains positive c.tables).value domains positive x : ℝ),
    fun x => by dsimp only; exact_mod_cast nonneg x, by
      dsimp only
      rw [← Rat.cast_sum]
      exact_mod_cast normalized⟩

/-- Configurations already contain the observation coordinates. Reading a
catalogue constraint is deterministic observation of that sampled world. -/
noncomputable def space
    (nonneg : ∀ x, 0 ≤ (combineAll domains positive c.tables).value domains positive x)
    (normalized : ∑ x : Config domains,
      (combineAll domains positive c.tables).value domains positive x = 1) :
    Model Unit (Config domains) (Config domains) Id where
  prior _ := c.prior domains positive nonneg normalized
  observations _ x := Prob.dirac x
  catalogue i x := decide (x (c.catalogue i).1 = (c.catalogue i).2)

omit [DecidableEq Id] in
theorem space_likelihood
    (nonneg : ∀ x, 0 ≤ (combineAll domains positive c.tables).value domains positive x)
    (normalized : ∑ x : Config domains,
      (combineAll domains positive c.tables).value domains positive x = 1)
    (E : Finset Id) (x : Config domains) :
    (c.space domains positive nonneg normalized).likelihood () E x =
      if satisfies domains (c.evidence domains E) x then 1 else 0 := by
  classical
  simp only [Model.likelihood, Model.accepts, space, Prob.dirac, decide_eq_true_eq]
  rw [Finset.sum_eq_single x]
  · simp [evidence, satisfies]
  · intro y _ hy; simp [hy]
  · simp

omit [DecidableEq Id] in
theorem answer_eq_space
    (nonneg : ∀ x, 0 ≤ (combineAll domains positive c.tables).value domains positive x)
    (normalized : ∑ x : Config domains,
      (combineAll domains positive c.tables).value domains positive x = 1)
    (E : Finset Id) (q : List (Constraint domains)) :
    (c.answer domains positive E q).map (fun r => (r : ℝ)) =
      (c.space domains positive nonneg normalized).probability? () E
        (fun x => decide (satisfies domains q x)) := by
  have castMass (cs : List (Constraint domains)) :
      (c.mass domains positive cs : ℝ) = ∑ x : Config domains,
        if satisfies domains cs x then
          ((combineAll domains positive c.tables).value domains positive x : ℝ) else 0 := by
    unfold mass
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  have z : (∑ x : Config domains,
      ((combineAll domains positive c.tables).value domains positive x : ℝ) *
        if satisfies domains (c.evidence domains E) x then 1 else 0) =
      (c.mass domains positive (c.evidence domains E) : ℝ) := by
    rw [castMass]
    simp only [mul_ite, mul_one, mul_zero]
  have num : (∑ x : Config domains, if satisfies domains q x then
      ((combineAll domains positive c.tables).value domains positive x : ℝ) *
        if satisfies domains (c.evidence domains E) x then 1 else 0 else 0) =
      (c.mass domains positive (c.evidence domains E ++ q) : ℝ) := by
    rw [castMass]
    apply Finset.sum_congr rfl
    intro x _
    simp only [satisfies_append]
    split_ifs <;> simp_all
  rw [Model.probability?_formula]
  simp only [Model.normalizer, Mettapedia.ProbabilityTheory.BayesianInference.evidence,
    space_likelihood]
  simp only [space, prior, decide_eq_true_eq, z, num]
  have pos : (0 : ℝ) < (c.mass domains positive (c.evidence domains E) : ℝ) ↔
      0 < c.mass domains positive (c.evidence domains E) := by norm_cast
  simp only [answer, pos]
  split_ifs <;> simp

/-- The rational implementation and real posterior share the same identified
ledger revision, as well as their query observations. -/
noncomputable def realBridge
    (nonneg : ∀ x, 0 ≤ (combineAll domains positive c.tables).value domains positive x)
    (normalized : ∑ x : Config domains,
      (combineAll domains positive c.tables).value domains positive x = 1) :
    letI := c.model domains positive
    letI := (c.space domains positive nonneg normalized).worldModel ()
    Mettapedia.Logic.WorldModel.RevisionMap (Finset Id) (List (Constraint domains)) (Option ℚ)
      (Finset Id) (Config domains → Bool) (Option ℝ) := by
  letI := c.model domains positive
  letI := (c.space domains positive nonneg normalized).worldModel ()
  exact {
    state := id
    query := fun q x => decide (satisfies domains q x)
    value := Option.map (fun r => (r : ℝ))
    observe := by
      intro E q
      change (c.space domains positive nonneg normalized).probability? () E
        (fun x => decide (satisfies domains q x)) = (c.answer domains positive E q).map (fun r : ℚ => (r : ℝ))
      have h := (c.answer_eq_space domains positive nonneg normalized E q).symm
      exact h.trans (by cases c.answer domains positive E q <;> rfl)
    empty := rfl
    revise := fun _ _ => rfl }

/-- A data-level admission check for the normalized prior used by `realBridge`.
The raw factor algebra also permits signed tables; those are not probabilities. -/
def checkPrior : Bool := decide
  ((∀ x : Config domains, 0 ≤ (combineAll domains positive c.tables).value domains positive x) ∧
    (∑ x : Config domains, (combineAll domains positive c.tables).value domains positive x) = 1)

omit [DecidableEq Id] in
theorem checkPrior_correct : c.checkPrior domains positive = true ↔
    ((∀ x : Config domains, 0 ≤ (combineAll domains positive c.tables).value domains positive x) ∧
    (∑ x : Config domains, (combineAll domains positive c.tables).value domains positive x) = 1) := by
  simp [checkPrior]

inductive AdmissionError where
  | invalidPrior
  deriving DecidableEq, Repr

/-- Admission failure, impossible evidence, and an answered zero are distinct. -/
def checkedEvaluate (log : List Id) (q : List (Constraint domains)) : Except AdmissionError (Option ℚ) :=
  if c.checkPrior domains positive then .ok (c.evaluate domains positive log q)
  else .error .invalidPrior

/-- The memoization key contains the actual factors and evidence, not merely
an outer space revision or a posterior number. -/
def request (log : List Id) (q : List (Constraint domains)) (revision : Nat) : QueryRequest domains where
  tables := c.tables
  evidence := log.eraseDups.map c.catalogue
  query := q
  order := c.order
  covers := c.covers
  spaceRevision := revision

theorem cached_query (history : List (QueryRequest domains)) (log : List Id)
    (q : List (Constraint domains)) (revision : Nat) :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.lookupOrCompute
      (QueryRequest.key domains) (QueryRequest.observe domains positive)
      (history.foldl (Mettapedia.GSLT.Dynamics.MemoizationObserver.store
        (QueryRequest.key domains) (QueryRequest.observe domains positive))
        Mettapedia.GSLT.Dynamics.MemoizationObserver.Table.empty)
      (c.request domains log q revision) = c.evaluate domains positive log q :=
  query_cache_answers domains positive history _

/-- Replaying an identity preserves the compiled answer. -/
theorem replay (log : List Id) (i : Id) (q : List (Constraint domains)) :
    c.evaluate domains positive (i :: i :: log) q = c.evaluate domains positive (i :: log) q := by
  rw [evaluate_correct, evaluate_correct]
  simp

/-- Retraction removes all deliveries of the identified observation. -/
def retract (log : List Id) (i : Id) : List Id := log.filter (· != i)

theorem retract_denote (log : List Id) (i : Id) :
    (retract log i).toFinset = log.toFinset.erase i := by ext j; simp [retract, and_comm, ne_comm]

theorem retract_answer (log : List Id) (i : Id) (q : List (Constraint domains)) :
    c.evaluate domains positive (retract log i) q =
      c.answer domains positive (log.toFinset.erase i) q := by
  rw [evaluate_correct, retract_denote]

end Context

/-- Explicit work states; the original ledger is retained in every phase. -/
inductive Term (Id : Type) (domains : Fin n → ℕ) where
  | request (log : List Id) (query : List (Constraint domains))
  | work (log : List Id) (order : List (Fin n)) (numerator denominator : List (Table domains))
  | done (log : List Id) (value : Option ℚ)

namespace Term
variable (c : Context Id domains)

def origin : Term Id domains → List Id
  | .request log _ | .work log _ _ _ | .done log _ => log

def finish (num den : List (Table domains)) : Option ℚ :=
  let z := (combineAll domains positive den).value domains positive (fun v => ⟨0, positive v⟩)
  if 0 < z then some ((combineAll domains positive num).value domains positive
    (fun v => ⟨0, positive v⟩) / z) else none

def next : Term Id domains → Option (Term Id domains)
  | .request log q => some (.work log c.order
      (queryTables domains positive c.tables (log.eraseDups.map c.catalogue ++ q))
      (queryTables domains positive c.tables (log.eraseDups.map c.catalogue)))
  | .work log (v :: vs) num den => some (.work log vs
      (eliminateVar domains positive num v) (eliminateVar domains positive den v))
  | .work log [] num den => some (.done log (finish domains positive num den))
  | .done _ _ => none

/-- Remaining exact work, used only as a proof invariant, not a transition oracle. -/
def value : Term Id domains → Option ℚ
  | .request log q => c.evaluate domains positive log q
  | .work _ order num den => finish domains positive
      (eliminateVars domains positive num order) (eliminateVars domains positive den order)
  | .done _ result => result

theorem next_value {s t : Term Id domains} (h : next domains positive c s = some t) :
    value domains positive c s = value domains positive c t := by
  cases s with
  | request log q => cases h; rfl
  | work log order num den =>
    cases order with
    | nil => cases h; rfl
    | cons v vs => cases h; rfl
  | done log result => cases h

theorem next_origin {s t : Term Id domains} (h : next domains positive c s = some t) :
    origin domains s = origin domains t := by
  cases s with
  | request log q => cases h; rfl
  | work log order num den => cases order <;> cases h <;> rfl
  | done log result => cases h

def theory : GSLT where
  Term := Term Id domains
  equations := Setoid.ker id
  rewrites s t := next domains positive c s = some t
  rewrites_resp_left := by intro s s' t h step; change s = s' at h; subst s'; exact ⟨t, step, rfl⟩
  rewrites_resp_right := by intro s t t' step h; change t = t' at h; subst t'; exact step

theorem path_invariant {S : GSLT} {V : Type} (obs : S.Term → V)
    (preserves : ∀ a b, S.Step a b → obs a = obs b) :
    ∀ {a b}, S.RewritePath a b → obs a = obs b
  | _, _, .nil _ => rfl
  | _, _, .cons h rest => (preserves _ _ h).trans (path_invariant obs preserves rest)

theorem path_value {s t : Term Id domains}
    (path : (theory domains positive c).RewritePath s t) :
    value domains positive c s = value domains positive c t :=
  path_invariant (S := theory domains positive c) (value domains positive c)
    (fun _ _ => next_value domains positive c) path

theorem path_origin {s t : Term Id domains}
    (path : (theory domains positive c).RewritePath s t) : origin domains s = origin domains t :=
  path_invariant (S := theory domains positive c) (origin domains)
    (fun _ _ => next_origin domains positive c) path

/-- The finite order supplies a terminating path; no completion is assumed. -/
def workPath (log : List Id) (order : List (Fin n)) (num den : List (Table domains)) :
    (theory domains positive c).RewritePath (.work log order num den)
      (.done log (value domains positive c (.work log order num den))) := by
  induction order generalizing num den with
  | nil => exact .cons rfl (.nil _)
  | cons v vs ih => exact .cons rfl (ih _ _)

def queryPath (log : List Id) (q : List (Constraint domains)) :
    (theory domains positive c).RewritePath (.request log q)
      (.done log (c.evaluate domains positive log q)) :=
  .cons rfl (workPath domains positive c log c.order _ _)

theorem normal_iff (s : Term Id domains) :
    (theory domains positive c).IsNormalForm s ↔ ∃ log v, s = .done log v := by
  cases s with
  | request log q =>
    constructor
    · intro h; exact (h ⟨_, rfl⟩).elim
    · rintro ⟨_, _, h⟩; cases h
  | work log order num den =>
    constructor
    · intro h; cases order <;> exact (h ⟨_, rfl⟩).elim
    · rintro ⟨_, _, h⟩; cases h
  | done log v =>
    constructor
    · intro _; exact ⟨log, v, rfl⟩
    · intro _ ⟨t, h⟩; cases h

/-- A first concrete inhabitant of the general exact-query operational contract. -/
noncomputable def exactMachine :
    letI := c.model domains positive
    ExactQueryGSLT (c.realization domains positive) := by
  letI := c.model domains positive
  exact {
    theory := theory domains positive c
    request := .request
    answer := .done
    executePath := queryPath domains positive c
    answer_normal log v := (normal_iff domains positive c _).mpr ⟨log, v, rfl⟩
    answer_reflect log q v path := (path_value domains positive c path).symm
    covered_normal log q terminal path normal := by
      obtain ⟨log', v, rfl⟩ := (normal_iff domains positive c terminal).mp normal
      have same := path_origin domains positive c path
      change log = log' at same
      subst log'
      exact ⟨v, rfl⟩ }

/-- The terminal observation is the independently defined finite weighted sum. -/
theorem terminal_exact (log : List Id) (q : List (Constraint domains)) (t : Term Id domains)
    (path : (theory domains positive c).RewritePath (.request log q) t)
    (normal : (theory domains positive c).IsNormalForm t) :
    t = .done log (c.answer domains positive log.toFinset q) := by
  let := c.model domains positive
  have h := (exactMachine domains positive c).covered_terminal_exact log q t path normal
  simpa only [exactMachine, Context.realization, Context.evaluate_correct] using h

/-- Fuel exhaustion leaves the work state intact, rather than fabricating a
completed impossible-evidence answer. -/
def run : Nat → Term Id domains → Term Id domains
  | 0, t => t
  | fuel + 1, t => match next domains positive c t with
    | none => t
    | some u => run fuel u

def result? : Term Id domains → Option (Option ℚ)
  | .done _ v => some v
  | _ => none

end Term
namespace Controls

abbrev domains3 : Fin 3 → Nat := fun _ => 2
theorem positive3 : ∀ i, 0 < domains3 i := fun _ => by norm_num [domains3]

def coin (p : ℚ) (b : Fin 2) : ℚ := if b = 1 then p else 1-p

def telemetry (yes no : ℚ) : Context Bool domains3 where
  tables := [tabulate domains3 positive3 [0,1,2] (by decide) (fun x =>
    1/2 * coin (if x 0 = 1 then yes else no) (x 1) *
      coin (if x 0 = 1 then yes else no) (x 2))]
  catalogue b := if b then ⟨2, 1⟩ else ⟨1, 1⟩
  order := [0,1,2]
  covers i := by fin_cases i <;> simp

def cause : List (Constraint domains3) := [⟨0, 1⟩]

theorem shared_cause_updated :
    (telemetry (3/4) (1/4)).evaluate domains3 positive3 [false, true] cause = some (9/10) := by
  decide +kernel

theorem prior_answer : (telemetry 1 (1/2)).evaluate domains3 positive3 [] cause = some (1/2) := by
  decide +kernel

theorem report_and_replay :
    (telemetry 1 (1/2)).evaluate domains3 positive3 [false] cause = some (2/3) ∧
    (telemetry 1 (1/2)).evaluate domains3 positive3 [false, false] cause = some (2/3) ∧
    (telemetry 1 (1/2)).evaluate domains3 positive3 [false, true] cause = some (4/5) := by
  decide +kernel

theorem machine_agrees :
    Term.result? domains3 (Term.run domains3 positive3 (telemetry 1 (1/2)) 5
      (.request [false, true] cause)) = some (some (4/5)) := by decide +kernel

theorem suspended_not_impossible :
    Term.result? domains3 (Term.run domains3 positive3 (telemetry 1 (1/2)) 2
      (.request [false, true] cause)) = none := by decide +kernel

def contradictory : Context Bool domains3 :=
  { telemetry 1 (1/2) with catalogue := fun b => if b then ⟨1, 0⟩ else ⟨1, 1⟩ }

theorem contradiction_and_retraction :
    contradictory.evaluate domains3 positive3 [false, true] cause = none ∧
    contradictory.evaluate domains3 positive3 (Context.retract [false, true] true) cause = some (2/3) := by
  decide +kernel

def observedFalse : Context Bool domains3 :=
  { telemetry 1 (1/2) with catalogue := fun _ => ⟨0, 0⟩ }

theorem zero_answer_not_impossible : observedFalse.evaluate domains3 positive3 [false] cause = some 0 := by
  decide +kernel

theorem parameters_change_answer :
    (telemetry 1 (1/2)).evaluate domains3 positive3 [false] cause = some (2/3) ∧
    (telemetry 1 (1/4)).evaluate domains3 positive3 [false] cause = some (4/5) := by
  decide +kernel

theorem changed_parameters_change_key :
    ((telemetry 1 (1/2)).request domains3 [false] cause 0).key domains3 ≠
      ((telemetry 1 (1/4)).request domains3 [false] cause 0).key domains3 := by
  intro equal
  have h := queryKey_sound domains3 positive3 _ _ equal
  have a : ((telemetry 1 (1/2)).request domains3 [false] cause 0).observe domains3 positive3 = some (2/3) := by decide +kernel
  have b : ((telemetry 1 (1/4)).request domains3 [false] cause 0).observe domains3 positive3 = some (4/5) := by decide +kernel
  rw [a, b] at h
  norm_num at h

theorem telemetry_nonnegative : ∀ x : Config domains3,
    0 ≤ (combineAll domains3 positive3 (telemetry 1 (1/2)).tables).value domains3 positive3 x := by decide +kernel

theorem telemetry_normalized : (∑ x : Config domains3,
    (combineAll domains3 positive3 (telemetry 1 (1/2)).tables).value domains3 positive3 x) = 1 := by decide +kernel

theorem real_probability_agrees :
    ((telemetry 1 (1/2)).space domains3 positive3 telemetry_nonnegative telemetry_normalized).probability?
      () {false, true} (fun x => decide (satisfies domains3 cause x)) = some (4/5) := by
  rw [← Context.answer_eq_space]
  have eq : ([false, true] : List Bool).toFinset = {false, true} := by simp
  rw [← eq, ← Context.evaluate_correct]
  rw [report_and_replay.2.2]
  norm_num

theorem checked_probabilities :
    (telemetry 1 (1/2)).checkedEvaluate domains3 positive3 [false, true] cause = .ok (some (4/5)) ∧
    (telemetry 2 (1/2)).checkedEvaluate domains3 positive3 [] cause = .error .invalidPrior := by
  decide +kernel

end Controls
end Mettapedia.Logic.WorldModel.DistributionalSpaceExecution
