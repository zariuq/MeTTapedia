import Mettapedia.GSLT.Causality.ContextBindings

/-!
# Structural models as a bubble: recursive models, feedback, and the GSLT that hosts both

A **structural model** gives every key a mechanism that reads the store
(`Mechanisms`).  A **solution** is a store every mechanism reproduces
(`IsSolution`).  An intervention replaces mechanisms by constants
(`surgery`), and `do` is that surgery.

**The GSLT top** (`modelGSLT`).  A term is a model with a store; one step
updates every key by its mechanism.  Any mechanisms are allowed, recursive or
not.  The solutions are exactly the terms that step to themselves
(`step_self_iff`).  Surgery is an override action (`surgeryAction`), so explicit
and derived `do` of `ContextBindings` both act on it.

**The recursive bubble** (`Recursive`): a rank, bounded, such that every
mechanism reads only keys of smaller rank (Halpern's recursive, or acyclic,
models).  Its guarantee, as theorems about the bubble:

* updating from any store for as many steps as the bound reaches a solution
  (`iterate_isSolution`), and the solution is unique (`solution_unique`,
  `exists_unique_solution`);
* every run of the GSLT from a recursive model reaches that solution and stays
  there (`run_reaches_solution`);
* surgery keeps a model recursive (`recursive_surgery`), so every intervened
  recursive model has a unique solution (`surgery_exists_unique_solution`).

**Feedback lies outside the bubble.**  Two mutually defined cells:
* copying (`copyLoop`: `x := y`, `y := x`) has two solutions
  (`copyLoop_two_solutions`);
* negating (`negLoop`: `x := ¬y`, `y := x`) has none (`negLoop_no_solution`), so
  in the GSLT no term of it ever stops changing (`negLoop_never_settles`).
Neither is recursive (`copyLoop_not_recursive`, `negLoop_not_recursive`), and
both are terms of the same GSLT as every recursive model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.StructuralModels

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ContextBindings

variable {Key : Type} {Value : Type}

/-- **Mechanisms**: for every key, a function of the whole store. -/
abbrev Mechanisms (Key Value : Type) := Key → (Key → Value) → Value

/-- A mechanism **depends only** on a set of keys. -/
def DependsOnly (mechanism : (Key → Value) → Value) (keys : Set Key) : Prop :=
  ∀ store store' : Key → Value, (∀ key ∈ keys, store key = store' key) → mechanism store = mechanism store'

/-- A **solution**: a store every mechanism reproduces. -/
def IsSolution (mechanisms : Mechanisms Key Value) (store : Key → Value) : Prop :=
  ∀ key, store key = mechanisms key store

/-- One synchronous update: every key takes its mechanism's value. -/
def update (mechanisms : Mechanisms Key Value) (store : Key → Value) : Key → Value :=
  fun key => mechanisms key store

theorem isSolution_iff_update (mechanisms : Mechanisms Key Value) (store : Key → Value) :
    IsSolution mechanisms store ↔ update mechanisms store = store :=
  ⟨fun solution => funext fun key => (solution key).symm,
    fun fixed key => (congrFun fixed key).symm⟩

/-- **Recursive models**: every mechanism reads only keys of smaller rank, and
the ranks are bounded. -/
structure Recursive (mechanisms : Mechanisms Key Value) where
  rank : Key → ℕ
  bound : ℕ
  rank_lt : ∀ key, rank key < bound
  depends : ∀ key, DependsOnly (mechanisms key) {other | rank other < rank key}

variable {mechanisms : Mechanisms Key Value}

/-- After `n` updates, two runs agree on every key of rank below `n`. -/
theorem iterate_agree (recursive : Recursive mechanisms) :
    ∀ (n : ℕ) (store store' : Key → Value) (key : Key), recursive.rank key < n →
      (update mechanisms)^[n] store key = (update mechanisms)^[n] store' key
  | 0, _, _, _, below => absurd below (Nat.not_lt_zero _)
  | n + 1, store, store', key, below => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply recursive.depends key
      intro other smaller
      exact iterate_agree recursive n store store' other (by
        have : recursive.rank other < recursive.rank key := smaller
        omega)

/-- **Updating as many times as the bound reaches a solution.** -/
theorem iterate_isSolution (recursive : Recursive mechanisms) (store : Key → Value) :
    IsSolution mechanisms ((update mechanisms)^[recursive.bound] store) := by
  intro key
  have same := iterate_agree recursive recursive.bound store (update mechanisms store) key
    (recursive.rank_lt key)
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at same
  exact same

/-- **The solution is unique.** -/
theorem solution_unique (recursive : Recursive mechanisms) {store store' : Key → Value}
    (solution : IsSolution mechanisms store) (solution' : IsSolution mechanisms store') :
    store = store' := by
  have agree : ∀ (n : ℕ) (key : Key), recursive.rank key < n → store key = store' key := by
    intro n
    induction n with
    | zero => intro _ below; exact absurd below (Nat.not_lt_zero _)
    | succ n inner =>
        intro key below
        rw [solution key, solution' key]
        apply recursive.depends key
        intro other smaller
        exact inner other (by
          have : recursive.rank other < recursive.rank key := smaller
          omega)
  funext key
  exact agree recursive.bound key (recursive.rank_lt key)

/-- **A recursive model has exactly one solution.** -/
theorem exists_unique_solution (recursive : Recursive mechanisms) (seed : Key → Value) :
    ∃! store, IsSolution mechanisms store :=
  ⟨_, iterate_isSolution recursive seed, fun _ solution =>
    solution_unique recursive solution (iterate_isSolution recursive seed)⟩

/-! ## Interventions are surgery -/

/-- **Surgery**: an assigned key's mechanism becomes the constant assigned. -/
def surgery (assignment : Key → Option Value) (mechanisms : Mechanisms Key Value) :
    Mechanisms Key Value :=
  fun key store => (assignment key).getD (mechanisms key store)

theorem surgery_none (mechanisms : Mechanisms Key Value) :
    surgery (fun _ => none) mechanisms = mechanisms :=
  rfl

theorem surgery_override (outer inner : Key → Option Value) (mechanisms : Mechanisms Key Value) :
    surgery (override outer inner) mechanisms = surgery outer (surgery inner mechanisms) := by
  funext key store
  simp only [surgery, override_apply]
  cases outer key <;> rfl

/-- **Surgery keeps a model recursive.** -/
def recursive_surgery (recursive : Recursive mechanisms) (assignment : Key → Option Value) :
    Recursive (surgery assignment mechanisms) where
  rank := recursive.rank
  bound := recursive.bound
  rank_lt := recursive.rank_lt
  depends key store store' agree := by
    simp only [surgery]
    cases assignment key with
    | none => exact recursive.depends key store store' agree
    | some _ => rfl

/-- **Every intervened recursive model has exactly one solution.** -/
theorem surgery_exists_unique_solution (recursive : Recursive mechanisms)
    (assignment : Key → Option Value) (seed : Key → Value) :
    ∃! store, IsSolution (surgery assignment mechanisms) store :=
  exists_unique_solution (recursive_surgery recursive assignment) seed

/-! ## The GSLT that hosts every model -/

/-- A model with its current store. -/
structure Config (Key Value : Type) where
  mechanisms : Mechanisms Key Value
  store : Key → Value

/-- One step updates every key. -/
def Steps (source target : Config Key Value) : Prop :=
  target = ⟨source.mechanisms, update source.mechanisms source.store⟩

variable (Key Value) in
/-- **The GSLT of structural models**, recursive or not. -/
abbrev modelGSLT : GSLT where
  Term := Config Key Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Steps
  rewrites_resp_left := by
    intro source source' target equal step
    have same : source = source' := equal
    subst same
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    have same : target = target' := equal
    subst same
    exact step

/-- **The solutions are the terms that step to themselves.** -/
theorem step_self_iff (config : Config Key Value) :
    (modelGSLT Key Value).Step config config ↔ IsSolution config.mechanisms config.store := by
  rw [isSolution_iff_update]
  constructor
  · intro step
    have := congrArg Config.store step
    exact this.symm
  · intro fixed
    change config = ⟨config.mechanisms, update config.mechanisms config.store⟩
    rw [fixed]

theorem iterate_steps (config : Config Key Value) (n : ℕ) :
    ∃ target, Relation.ReflTransGen (modelGSLT Key Value).Step config target ∧
      target = ⟨config.mechanisms, (update config.mechanisms)^[n] config.store⟩ := by
  induction n with
  | zero => exact ⟨config, Relation.ReflTransGen.refl, rfl⟩
  | succ n inner =>
      obtain ⟨target, run, same⟩ := inner
      refine ⟨_, run.tail (show (modelGSLT Key Value).Step target _ from rfl), ?_⟩
      subst same
      rw [Function.iterate_succ_apply']

/-- **Every run of a recursive model reaches its solution and stays there.** -/
theorem run_reaches_solution (recursive : Recursive mechanisms) (store : Key → Value) :
    ∃ solution, Relation.ReflTransGen (modelGSLT Key Value).Step ⟨mechanisms, store⟩
        ⟨mechanisms, solution⟩ ∧
      IsSolution mechanisms solution ∧
        ∀ next, (modelGSLT Key Value).Step ⟨mechanisms, solution⟩ next → next = ⟨mechanisms, solution⟩ := by
  obtain ⟨target, run, same⟩ := iterate_steps ⟨mechanisms, store⟩ recursive.bound
  refine ⟨(update mechanisms)^[recursive.bound] store, same ▸ run,
    iterate_isSolution recursive store, fun next step => ?_⟩
  have fixed := (isSolution_iff_update _ _).mp (iterate_isSolution recursive store)
  change next = ⟨mechanisms, update mechanisms _⟩ at step
  rw [step, fixed]

/-- Surgery acts on configurations: the override action of interventions. -/
def surgeryAction : OverrideAction (modelGSLT Key Value) Key Value where
  assign assignment config :=
    ⟨surgery assignment config.mechanisms, fun key => (assignment key).getD (config.store key)⟩
  assign_none _ := rfl
  assign_override outer inner config := by
    change (⟨surgery (override outer inner) config.mechanisms, _⟩ : Config Key Value) =
      ⟨surgery outer (surgery inner config.mechanisms), _⟩
    rw [surgery_override]
    congr 1
    funext key
    rw [override_apply]
    cases outer key <;> rfl
  assign_resp _ left right equivalent := by
    have equal : left = right := equivalent
    subst equal
    rfl

/-! ## Feedback -/

/-- Two cells. -/
inductive Cell where
  | x
  | y
  deriving DecidableEq

/-- `x := y`, `y := x`. -/
def copyLoop : Mechanisms Cell Bool
  | .x, store => store .y
  | .y, store => store .x

/-- `x := ¬y`, `y := x`. -/
def negLoop : Mechanisms Cell Bool
  | .x, store => !store .y
  | .y, store => store .x

/-- **Copying has two solutions.** -/
theorem copyLoop_two_solutions :
    IsSolution copyLoop (fun _ => false) ∧ IsSolution copyLoop (fun _ => true) ∧
      (fun _ : Cell => false) ≠ fun _ => true := by
  refine ⟨fun key => by cases key <;> rfl, fun key => by cases key <;> rfl, fun same => ?_⟩
  exact Bool.false_ne_true (congrFun same .x)

/-- **Negating has no solution.** -/
theorem negLoop_no_solution (store : Cell → Bool) : ¬ IsSolution negLoop store := by
  intro solution
  have first := solution .x
  have second := solution .y
  simp only [negLoop] at first second
  rw [second] at first
  cases store .x <;> simp at first

/-- **In the GSLT, no term of the negating loop ever settles.** -/
theorem negLoop_never_settles (store : Cell → Bool) :
    ¬ (modelGSLT Cell Bool).Step ⟨negLoop, store⟩ ⟨negLoop, store⟩ :=
  fun step => negLoop_no_solution store ((step_self_iff _).mp step)

/-- **Copying is not recursive.** -/
theorem copyLoop_not_recursive : Recursive copyLoop → False := by
  intro recursive
  obtain ⟨falseSolution, trueSolution, different⟩ := copyLoop_two_solutions
  exact different (solution_unique recursive falseSolution trueSolution)

/-- **Negating is not recursive.** -/
theorem negLoop_not_recursive : Recursive negLoop → False := fun recursive =>
  negLoop_no_solution _ (iterate_isSolution recursive fun _ => false)

end Mettapedia.GSLT.Causality.StructuralModels
