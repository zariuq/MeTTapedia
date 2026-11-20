import Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationPlan

/-!
# Retained tables for exact evidence updates

A compiled elimination plan has stable input slots. The runtime retains each
intermediate rational table and the input slots on which it depends.
Replacement rebuilds dependent nodes and keeps the other tables. The
execution count measures newly materialized intermediate tables.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationPlan

open ExecutableFactorTable

variable {n m : Nat} {domains : Fin n → Nat}

def inputs : EliminationPlan n m → Finset (Fin m)
  | .unit => ∅
  | .input slot => {slot}
  | .mul left right => left.inputs ∪ right.inputs
  | .sumOut _ body => body.inputs

def operations : EliminationPlan n m → Nat
  | .unit | .input _ => 0
  | .mul left right => left.operations + right.operations + 1
  | .sumOut _ body => body.operations + 1

def affected (slot : Fin m) : EliminationPlan n m → Nat
  | .unit | .input _ => 0
  | .mul left right =>
    if slot ∈ left.inputs ∪ right.inputs then left.affected slot + right.affected slot + 1 else 0
  | .sumOut _ body => if slot ∈ body.inputs then body.affected slot + 1 else 0

theorem affected_le (slot : Fin m) (plan : EliminationPlan n m) :
    plan.affected slot ≤ plan.operations := by
  induction plan with
  | unit | input => exact Nat.le_refl _
  | mul left right ihl ihr =>
    simp only [affected, operations]
    split <;> omega
  | sumOut v body ih =>
    simp only [affected, operations]
    split <;> omega

inductive Cache (domains : Fin n → Nat) (m : Nat) : EliminationPlan n m → Type where
  | unit (value : Table domains) : Cache domains m .unit
  | input (slot : Fin m) (value : Table domains) : Cache domains m (.input slot)
  | mul {left right : EliminationPlan n m} (a : Cache domains m left) (b : Cache domains m right)
      (value : Table domains) (support : Finset (Fin m)) : Cache domains m (.mul left right)
  | sumOut {body : EliminationPlan n m} (v : Fin n) (child : Cache domains m body)
      (value : Table domains) (support : Finset (Fin m)) : Cache domains m (.sumOut v body)

namespace Cache

def table {plan : EliminationPlan n m} : Cache domains m plan → Table domains
  | .unit value | .input _ value | .mul _ _ value _ | .sumOut _ _ value _ => value

def support {plan : EliminationPlan n m} : Cache domains m plan → Finset (Fin m)
  | .unit _ => ∅
  | .input slot _ => {slot}
  | .mul _ _ _ slots | .sumOut _ _ _ slots => slots

private def combine (positive : ∀ v, 0 < domains v) {left right : EliminationPlan n m}
    (a : Cache domains m left) (b : Cache domains m right) : Cache domains m (.mul left right) :=
  .mul a b (a.table.mul domains positive b.table) (a.support ∪ b.support)

private def eliminate (positive : ∀ v, 0 < domains v) {body : EliminationPlan n m}
    (v : Fin n) (child : Cache domains m body) : Cache domains m (.sumOut v body) :=
  .sumOut v child (child.table.sumOut domains positive v) child.support

def build (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains) :
    (plan : EliminationPlan n m) → Cache domains m plan
  | .unit => .unit (ExecutableFactorTable.one domains positive)
  | .input slot => .input slot (tables slot)
  | .mul left right => combine positive (build positive tables left) (build positive tables right)
  | .sumOut v body => eliminate positive v (build positive tables body)

@[simp] theorem build_table (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (plan : EliminationPlan n m) : (build positive tables plan).table = plan.evaluate positive tables := by
  induction plan with
  | unit | input => rfl
  | mul left right ihl ihr =>
    change (build positive tables left).table.mul domains positive (build positive tables right).table =
      (left.evaluate positive tables).mul domains positive (right.evaluate positive tables)
    rw [ihl, ihr]
  | sumOut v body ih =>
    change (build positive tables body).table.sumOut domains positive v =
      (body.evaluate positive tables).sumOut domains positive v
    rw [ih]

@[simp] theorem build_support (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (plan : EliminationPlan n m) : (build positive tables plan).support = plan.inputs := by
  induction plan with
  | unit | input => rfl
  | mul left right ihl ihr =>
    change (build positive tables left).support ∪ (build positive tables right).support =
      left.inputs ∪ right.inputs
    rw [ihl, ihr]
  | sumOut v body ih => exact ih

private theorem build_update_of_absent (positive : ∀ v, 0 < domains v)
    (tables : Fin m → Table domains) (slot : Fin m) (replacement : Table domains)
    (plan : EliminationPlan n m) (absent : slot ∉ plan.inputs) :
    build positive (Function.update tables slot replacement) plan = build positive tables plan := by
  induction plan with
  | unit => rfl
  | input i =>
    have different : i ≠ slot := by simpa [inputs, eq_comm] using absent
    simp [build, Function.update_of_ne different]
  | mul left right ihl ihr =>
    simp only [inputs, Finset.mem_union, not_or] at absent
    simp only [build, ihl absent.1, ihr absent.2]
  | sumOut v body ih =>
    simp only [build, ih (by simpa only [inputs] using absent)]

/-- Replace one factor. Subtrees whose support excludes the slot keep their
cached tables, and factor values of zero use the same update path as others. -/
def refresh (positive : ∀ v, 0 < domains v) (slot : Fin m) (replacement : Table domains) :
    {plan : EliminationPlan n m} → Cache domains m plan → Cache domains m plan × Nat :=
  fun {_} old =>
    if slot ∈ old.support then
      match old with
      | .unit value => (.unit value, 0)
      | .input i _ => (.input i replacement, 0)
      | .mul left right _ slots =>
        let a := refresh positive slot replacement left
        let b := refresh positive slot replacement right
        (.mul a.1 b.1 (a.1.table.mul domains positive b.1.table) slots, a.2 + b.2 + 1)
      | .sumOut v child _ slots =>
        let next := refresh positive slot replacement child
        (.sumOut v next.1 (next.1.table.sumOut domains positive v) slots, next.2 + 1)
    else (old, 0)

/-- The runtime result agrees with rebuilding the cache from the changed
inputs, and its work counter is determined by the dependency structure. -/
theorem refresh_build (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (slot : Fin m) (replacement : Table domains) (plan : EliminationPlan n m) :
    refresh positive slot replacement (build positive tables plan) =
      (build positive (Function.update tables slot replacement) plan, plan.affected slot) := by
  induction plan with
  | unit => rfl
  | input i =>
    by_cases same : i = slot
    · subst i
      simp [refresh, build, support, affected]
    · simp [refresh, build, support, affected, Function.update_of_ne same, Ne.symm same]
  | mul left right ihl ihr =>
    change (if slot ∈ (build positive tables left).support ∪ (build positive tables right).support then
      let a := refresh positive slot replacement (build positive tables left)
      let b := refresh positive slot replacement (build positive tables right)
      (.mul a.1 b.1 (a.1.table.mul domains positive b.1.table)
        ((build positive tables left).support ∪ (build positive tables right).support),
        a.2 + b.2 + 1)
      else (build positive tables (.mul left right), 0)) = _
    rw [build_support, build_support]
    by_cases inside : slot ∈ left.inputs ∪ right.inputs
    · simp only [if_pos inside, affected, ihl, ihr, build, combine, build_support]
    · have absent : slot ∉ (.mul left right : EliminationPlan n m).inputs := inside
      rw [if_neg inside, build_update_of_absent positive tables slot replacement _ absent]
      simp only [affected, if_neg inside]
  | sumOut v body ih =>
    change (if slot ∈ (build positive tables body).support then
      let next := refresh positive slot replacement (build positive tables body)
      (.sumOut v next.1 (next.1.table.sumOut domains positive v)
        (build positive tables body).support, next.2 + 1)
      else (build positive tables (.sumOut v body), 0)) = _
    rw [build_support]
    by_cases inside : slot ∈ body.inputs
    · simp only [if_pos inside, affected, ih, build, eliminate, build_support]
    · have absent : slot ∉ (.sumOut v body : EliminationPlan n m).inputs := inside
      rw [if_neg inside, build_update_of_absent positive tables slot replacement _ absent]
      simp only [affected, if_neg inside]

end Cache

/-- A checked cache is tied to the actual contents of the factor slots. -/
structure Retained (positive : ∀ v, 0 < domains v) (plan : EliminationPlan n m)
    (tables : Fin m → Table domains) where
  cache : Cache domains m plan
  exact : cache = Cache.build positive tables plan

namespace Retained

def fromInputs (positive : ∀ v, 0 < domains v) (plan : EliminationPlan n m)
    (tables : Fin m → Table domains) : Retained positive plan tables :=
  ⟨Cache.build positive tables plan, rfl⟩

def table {positive : ∀ v, 0 < domains v} {plan : EliminationPlan n m}
    {tables : Fin m → Table domains} (state : Retained positive plan tables) : Table domains :=
  state.cache.table

theorem table_exact {positive : ∀ v, 0 < domains v} {plan : EliminationPlan n m}
    {tables : Fin m → Table domains} (state : Retained positive plan tables) :
    state.table = plan.evaluate positive tables := by
  rw [table, state.exact, Cache.build_table]

def replace {positive : ∀ v, 0 < domains v} {plan : EliminationPlan n m}
    {tables : Fin m → Table domains} (state : Retained positive plan tables)
    (slot : Fin m) (replacement : Table domains) :
    Retained positive plan (Function.update tables slot replacement) × Nat :=
  let result := state.cache.refresh positive slot replacement
  (⟨result.1, by
    dsimp only [result]
    rw [state.exact, Cache.refresh_build]⟩, result.2)

theorem replace_work {positive : ∀ v, 0 < domains v} {plan : EliminationPlan n m}
    {tables : Fin m → Table domains} (state : Retained positive plan tables)
    (slot : Fin m) (replacement : Table domains) :
    (state.replace slot replacement).2 = plan.affected slot := by
  change (state.cache.refresh positive slot replacement).2 = plan.affected slot
  rw [state.exact, Cache.refresh_build]

/-- A later value at the same factor slot supersedes the earlier value,
including when the earlier factor had zeros. -/
theorem replace_twice_table {positive : ∀ v, 0 < domains v} {plan : EliminationPlan n m}
    {tables : Fin m → Table domains} (state : Retained positive plan tables) (slot : Fin m)
    (first second : Table domains) :
    (((state.replace slot first).1.replace slot second).1).table =
      (state.replace slot second).1.table := by
  simp only [table_exact, Function.update_idem]

theorem updated_scopes (tables : Fin m → Table domains) (scopes : Fin m → List (Fin n))
    (agrees : ∀ i, (tables i).scope = scopes i)
    (slot : Fin m) (replacement : Table domains) (same : replacement.scope = scopes slot) :
    ∀ i, (Function.update tables slot replacement i).scope = scopes i := by
  intro i
  by_cases equal : i = slot
  · subst i
    simpa only [Function.update_self] using same
  · simpa only [Function.update_of_ne equal] using agrees i

/-- A scope-preserving evidence edit to a compiled plan gives exactly the
table computed by fresh bucket elimination. -/
theorem replace_compile_exact {positive : ∀ v, 0 < domains v}
    {tables : Fin m → Table domains} {scopes : Fin m → List (Fin n)}
    {order : List (Fin n)} (state : Retained positive (compile scopes order) tables)
    (agrees : ∀ i, (tables i).scope = scopes i)
    (slot : Fin m) (replacement : Table domains) (same : replacement.scope = scopes slot) :
    (state.replace slot replacement).1.table =
      ExecutableFactorTable.combineAll domains positive
        (ExecutableFactorTable.eliminateVars domains positive
          (List.ofFn (Function.update tables slot replacement)) order) := by
  rw [table_exact, evaluate_compile positive _ scopes (updated_scopes tables scopes agrees slot replacement same)]

end Retained

/-- A prepared schedule keeps the input scope of every factor slot explicit.
The public replacement operation checks that its schedule remains applicable. -/
structure Runtime (positive : ∀ v, 0 < domains v) (scopes : Fin m → List (Fin n))
    (order : List (Fin n)) where
  factors : Vector (Table domains) m
  scopes_match : ∀ i : Fin m, factors[i].scope = scopes i
  retained : Retained positive (compile scopes order) (fun i : Fin m => factors[i])

namespace Runtime

variable {positive : ∀ v, 0 < domains v} {scopes : Fin m → List (Fin n)}
variable {order : List (Fin n)}

def prepare (positive : ∀ v, 0 < domains v) (factors : Vector (Table domains) m)
    (order : List (Fin n)) : Runtime positive (fun i : Fin m => factors[i].scope) order :=
  ⟨factors, fun _ => rfl, Retained.fromInputs positive _ (fun i : Fin m => factors[i])⟩

def table (runtime : Runtime positive scopes order) : Table domains :=
  runtime.retained.table

theorem table_exact (runtime : Runtime positive scopes order) :
    runtime.table = ExecutableFactorTable.combineAll domains positive
      (ExecutableFactorTable.eliminateVars domains positive
        (List.ofFn (fun i : Fin m => runtime.factors[i])) order) := by
  rw [table, Retained.table_exact, evaluate_compile positive _ scopes runtime.scopes_match]

private theorem vector_set_eq_update (factors : Vector (Table domains) m)
    (slot : Fin m) (replacement : Table domains) :
    (fun i : Fin m => (factors.set slot.val replacement slot.isLt)[i]) =
      Function.update (fun i : Fin m => factors[i]) slot replacement := by
  funext i
  by_cases same : i = slot
  · subst i
    simp
  · rw [Function.update_of_ne same]
    exact Vector.getElem_set_ne slot.isLt i.isLt
      (fun equal => same (Fin.ext equal.symm))

def tryReplace (runtime : Runtime positive scopes order) (slot : Fin m)
    (replacement : Table domains) : Option (Runtime positive scopes order × Nat) :=
  if same : replacement.scope = scopes slot then
    let edited := runtime.factors.set slot.val replacement slot.isLt
    let next := runtime.retained.replace slot replacement
    have equal := vector_set_eq_update runtime.factors slot replacement
    some (⟨edited, fun i => by
      change ((fun j : Fin m => edited[j]) i).scope = scopes i
      rw [equal]
      exact Retained.updated_scopes _ scopes runtime.scopes_match slot replacement same i,
      equal.symm ▸ next.1⟩, next.2)
  else none

theorem tryReplace_rejects (runtime : Runtime positive scopes order) (slot : Fin m)
    (replacement : Table domains) (changed : replacement.scope ≠ scopes slot) :
    runtime.tryReplace slot replacement = none := by
  simp [tryReplace, changed]

theorem tryReplace_factors (runtime updated : Runtime positive scopes order) (slot : Fin m)
    (replacement : Table domains) (work : Nat)
    (accepted : runtime.tryReplace slot replacement = some (updated, work)) :
    updated.factors = runtime.factors.set slot.val replacement slot.isLt := by
  unfold tryReplace at accepted
  split at accepted
  · exact (congrArg (fun result => result.1.factors) (Option.some.inj accepted)).symm
  · contradiction

theorem tryReplace_work (runtime updated : Runtime positive scopes order) (slot : Fin m)
    (replacement : Table domains) (work : Nat)
    (accepted : runtime.tryReplace slot replacement = some (updated, work)) :
    work = (compile scopes order).affected slot := by
  unfold tryReplace at accepted
  split at accepted
  · have count := congrArg Prod.snd (Option.some.inj accepted)
    change (runtime.retained.replace slot replacement).2 = work at count
    rw [← count, Retained.replace_work]
  · contradiction

end Runtime
end Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationPlan
