import Mettapedia.GSLT.LanguageDef.DestinationPassingActivation

/-!
# Output-first refines output-at-return

Two disciplines run the same equations.  **Output at return** is the
defunctionalized machine `DefunctionalizedEquationBodies.compiled`: a callee
returns its value, the caller unifies its pattern with it when the frame
resumes, and a `let` binds its pattern after its bound body.  **Output first**
is `outputFirst` (`DestinationPassingActivation`): the destination is met at
activation, a `let` binds its pattern before its bound body
(`BindsAhead`), a conditional meets the destination before the branch, and a
return does not unify.  Both are instances of the generic shared-continuation
machine, whose `step` expands the first task of an ordered frontier.

**The result.**  For programs `PA`, `PF` with the same heads whose bodies are
related by `BindsAhead []` (`ProgramBindsAhead`; `SProgram.normalize` and
`SProgram.normalizeFirst` are, `programBindsAhead_normalize`), and states that
start related, `outputFirst_simulates`: after any `n` output-at-return steps
there is `n' ≤ n` such that the output-first frontier after `n'` steps is the
output-at-return frontier with some tasks removed, every remaining pair related,
and the answers delivered so far correspond one to one, in order.  Hence

* `outputFirst_answers` (the prefix law): every answer list the output-at-return
  machine has delivered within `n` steps, the output-first machine has delivered
  within some `n' ≤ n` steps; since answers only accumulate
  (`emitted_repeats_prefix`), the output-first stream is at least as defined in
  the prefix order;
* `outputFirst_terminates`: when the output-at-return run exhausts its frontier
  within `n` steps, the output-first run exhausts its own within `n' ≤ n`, with
  the same ordered answer list.

`outputFirst_at_least_as_defined` states the prefix law against any later
output-first state.  Corresponding answers carry the same value and consistent
stores with the same solutions and supply (`SameAnswer`).  Over the substitution
store (`substitutionExact`, built on `unifyTotal_mgu`, `unifyTotal_sound`,
`unifyTotal_relevantIdempotent` and `unifyTotal_none_iff_not_unifiable`) that
makes the two stores instances of each other (`sameAnswer_instances`), hence
variants (`sameAnswer_variant`): the same answers up to renaming.

**Why.**  Every unification either side performs is an equation between the
same terms, and an exact store (`ExactStore`) denotes the set of valuations
satisfying the equations made so far: unification intersects it with the
solutions of one more equation (`ExactStore.unify_some`), so the order of
unifications does not matter.  An output-first task has made the equations its
output-at-return counterpart still owes (`pending`: bindings made ahead, and the
exposed output meeting the destination, at every level of the return stack), so
its store denotes the counterpart's store intersected with them (`Related`).
When that intersection becomes empty the output-first side fails and the
output-at-return task, and everything it will ever spawn, can deliver no answer
(`Doomed`, `expand_doomed`): it is dropped from the correspondence while the
output-at-return machine keeps spending steps on it.  This is where the
output-first run can terminate while the other does not.

**Tests and primitives.**  They read the store, and the output-first store has
more bindings.  The theorem assumes `Moded`: every test and primitive the
output-at-return run evaluates gives the same result on every consistent
refinement of its store.  It holds when tests and primitives do not depend on
bindings (`moded_of_stable`, `substitution_moded`), in particular for programs
without them, and, over the substitution store, at every test or primitive whose
arguments the store already determines (`substitution_stable_of_ground`).  It is
needed: in `DestinationPassingControls.prim_counterexample` a primitive's
argument is bound only by the destination, output first delivers an answer that
output at return never does, and the run is not moded
(`prim_counterexample_not_moded`).  A late binding repeated on the output-first
side adds no constraint (`ExactStore.unify_entailed`).

**Scope.**  The theorems hold from any corresponding states; two starting
points are provided: a query run as a control whose call's pattern is the
destination (`queryState`, `simulates_query`, `source_outputFirst_answers`), and
`DefunctionalizedEquationBodies.initial`, a call without destination
(`simulates_initial`).  Answers are compared up to the solutions of their
stores, not term by term; step counts are steps of the generic machine, not
costs.  Not proved: that a given run is moded (only the pointwise criteria
above), and that the repeated late binding leaves a substitution store unchanged
term by term (only its solutions).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DestinationPassing

open Mettapedia.Machines.SharedContinuation
open DefunctionalizedEquationBodies
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Simulation of ordered frontiers -/

section Frontier

variable {Context Control Call Frame Answer : Type}

/-- The tasks and answers a task yields at the head of the frontier, once its
control has reached `instruction`. -/
def expandWith (P : Program Context Control Call Frame Answer) (context : Context)
    (returns : List Frame) :
    Instruction Call Frame Answer → List (Task Context Control Frame) × List (Context × Answer)
  | .ret value =>
      match returns with
      | [] => ([], [(context, value)])
      | f :: pending =>
          ([⟨(P.resume context f value).1, (P.resume context f value).2, pending⟩], [])
  | .fail => ([], [])
  | .call callee f =>
      ((P.branches context callee).map fun next => ⟨next.1, next.2, f :: returns⟩, [])
  | .tail callee =>
      ((P.branches context callee).map fun next => ⟨next.1, next.2, returns⟩, [])

/-- The tasks and answers one task yields at the head of the frontier. -/
def expand (P : Program Context Control Call Frame Answer) (t : Task Context Control Frame) :
    List (Task Context Control Frame) × List (Context × Answer) :=
  expandWith P t.context t.returns (P.inspect t.control)

theorem step_cons (P : Program Context Control Call Frame Answer)
    (t : Task Context Control Frame) (rest : List (Task Context Control Frame))
    (emitted : List (Context × Answer)) :
    step P ⟨t :: rest, emitted⟩ = ⟨(expand P t).1 ++ rest, emitted ++ (expand P t).2⟩ := by
  simp only [step, expand]
  cases P.inspect t.control with
  | ret value => cases t.returns <;> simp [expandWith]
  | fail => simp [expandWith]
  | call callee f => simp [expandWith]
  | tail callee => simp [expandWith]

theorem emitted_step_prefix (P : Program Context Control Call Frame Answer)
    (s : State Context Control Frame Answer) : s.emitted <+: (step P s).emitted := by
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => exact List.prefix_refl _
  | cons t rest =>
      rw [step_cons]
      exact List.prefix_append _ _

/-- Answers only accumulate. -/
theorem emitted_repeats_prefix (P : Program Context Control Call Frame Answer) :
    ∀ (n m : ℕ) (s : State Context Control Frame Answer), n ≤ m →
      (repeats (step P) n s).emitted <+: (repeats (step P) m s).emitted
  | 0, 0, _, _ => List.prefix_refl _
  | 0, m + 1, s, _ =>
      (emitted_step_prefix P s).trans (emitted_repeats_prefix P 0 m (step P s) (Nat.zero_le _))
  | n + 1, 0, _, le => absurd le (by omega)
  | n + 1, m + 1, s, le => emitted_repeats_prefix P n m (step P s) (by omega)

/-- `Embeds R D as bs`: `bs` is `as` with some tasks satisfying `D` removed, and
every remaining task related by `R` to its counterpart in `bs`. -/
inductive Embeds {α β : Type} (R : α → β → Prop) (D : α → Prop) : List α → List β → Prop
  | nil : Embeds R D [] []
  | keep {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Embeds R D as bs → Embeds R D (a :: as) (b :: bs)
  | drop {a : α} {as : List α} {bs : List β} : D a → Embeds R D as bs → Embeds R D (a :: as) bs

namespace Embeds

variable {α β : Type} {R : α → β → Prop} {D : α → Prop}

theorem append {as as' : List α} {bs bs' : List β} (first : Embeds R D as bs)
    (second : Embeds R D as' bs') : Embeds R D (as ++ as') (bs ++ bs') := by
  induction first with
  | nil => exact second
  | keep r _ ih => exact .keep r ih
  | drop d _ ih => exact .drop d ih

theorem prepend {as rest : List α} {bs : List β} (all : ∀ a ∈ as, D a)
    (h : Embeds R D rest bs) : Embeds R D (as ++ rest) bs := by
  induction as with
  | nil => exact h
  | cons a as ih =>
      exact .drop (all a List.mem_cons_self)
        (ih fun x member => all x (List.mem_cons_of_mem _ member))

theorem of_forall {as : List α} (all : ∀ a ∈ as, D a) : Embeds R D as [] := by
  simpa using prepend (bs := []) all (Embeds.nil (R := R) (D := D))

theorem eq_nil {bs : List β} (h : Embeds R D [] bs) : bs = [] := by
  cases h
  rfl

end Embeds

variable {C₁ K₁ Call₁ F₁ A₁ C₂ K₂ Call₂ F₂ A₂ : Type}

/-- Two states correspond: the second frontier embeds in the first, and the
answers delivered so far correspond pairwise, in order. -/
def Simulates (R : Task C₁ K₁ F₁ → Task C₂ K₂ F₂ → Prop) (D : Task C₁ K₁ F₁ → Prop)
    (Same : C₁ × A₁ → C₂ × A₂ → Prop) (s₁ : State C₁ K₁ F₁ A₁) (s₂ : State C₂ K₂ F₂ A₂) :
    Prop :=
  Embeds R D s₁.frontier s₂.frontier ∧ List.Forall₂ Same s₁.emitted s₂.emitted

/-- One step of the first machine is matched by one step of the second, or by
none when it expands a removed task. -/
theorem simulates_step (P₁ : Program C₁ K₁ Call₁ F₁ A₁) (P₂ : Program C₂ K₂ Call₂ F₂ A₂)
    {R : Task C₁ K₁ F₁ → Task C₂ K₂ F₂ → Prop} {D : Task C₁ K₁ F₁ → Prop}
    {Same : C₁ × A₁ → C₂ × A₂ → Prop} (M : Task C₁ K₁ F₁ → Prop)
    (related : ∀ a b, R a b → M a →
      Embeds R D (expand P₁ a).1 (expand P₂ b).1 ∧
        List.Forall₂ Same (expand P₁ a).2 (expand P₂ b).2)
    (doomed : ∀ a, D a → (∀ a' ∈ (expand P₁ a).1, D a') ∧ (expand P₁ a).2 = [])
    {s₁ : State C₁ K₁ F₁ A₁} {s₂ : State C₂ K₂ F₂ A₂} (sim : Simulates R D Same s₁ s₂)
    (moded : ∀ a ∈ s₁.frontier, M a) :
    Simulates R D Same (step P₁ s₁) (step P₂ s₂) ∨ Simulates R D Same (step P₁ s₁) s₂ := by
  obtain ⟨embeds, answers⟩ := sim
  rcases s₁ with ⟨frontier₁, emitted₁⟩
  rcases s₂ with ⟨frontier₂, emitted₂⟩
  cases embeds with
  | nil => exact .inl ⟨.nil, answers⟩
  | @keep a b rest₁ rest₂ r rest =>
      obtain ⟨tasks, delivered⟩ := related a b r (moded a List.mem_cons_self)
      refine .inl ?_
      rw [step_cons, step_cons]
      exact ⟨tasks.append rest, List.rel_append answers delivered⟩
  | @drop a rest₁ _ d rest =>
      obtain ⟨all, none⟩ := doomed a d
      refine .inr ?_
      rw [step_cons]
      refine ⟨Embeds.prepend all rest, ?_⟩
      simpa [none] using answers

/-- **Simulation of runs.**  After `n` steps of the first machine, the second
has taken `n' ≤ n` steps and the states still correspond. -/
theorem simulates_repeats (P₁ : Program C₁ K₁ Call₁ F₁ A₁) (P₂ : Program C₂ K₂ Call₂ F₂ A₂)
    {R : Task C₁ K₁ F₁ → Task C₂ K₂ F₂ → Prop} {D : Task C₁ K₁ F₁ → Prop}
    {Same : C₁ × A₁ → C₂ × A₂ → Prop} (M : Task C₁ K₁ F₁ → Prop)
    (related : ∀ a b, R a b → M a →
      Embeds R D (expand P₁ a).1 (expand P₂ b).1 ∧
        List.Forall₂ Same (expand P₁ a).2 (expand P₂ b).2)
    (doomed : ∀ a, D a → (∀ a' ∈ (expand P₁ a).1, D a') ∧ (expand P₁ a).2 = []) :
    ∀ (n : ℕ) (s₁ : State C₁ K₁ F₁ A₁) (s₂ : State C₂ K₂ F₂ A₂), Simulates R D Same s₁ s₂ →
      (∀ m < n, ∀ a ∈ (repeats (step P₁) m s₁).frontier, M a) →
      ∃ n' ≤ n, Simulates R D Same (repeats (step P₁) n s₁) (repeats (step P₂) n' s₂)
  | 0, _, _, sim, _ => ⟨0, le_rfl, sim⟩
  | n + 1, s₁, s₂, sim, moded => by
      have later : ∀ m < n, ∀ a ∈ (repeats (step P₁) m (step P₁ s₁)).frontier, M a :=
        fun m below => moded (m + 1) (by omega)
      rcases simulates_step P₁ P₂ M related doomed sim (moded 0 (Nat.succ_pos n)) with
        both | first
      · obtain ⟨n', le, sim'⟩ :=
          simulates_repeats P₁ P₂ M related doomed n _ _ both later
        exact ⟨n' + 1, by omega, sim'⟩
      · obtain ⟨n', le, sim'⟩ :=
          simulates_repeats P₁ P₂ M related doomed n _ _ first later
        exact ⟨n', by omega, sim'⟩

end Frontier

/-! ## Exact stores -/

section Exact

variable {Term Store Op : Type}

/-- A store algebra whose unification is exact when stores are read as sets of
solutions: a well-formed store denotes the valuations solving the equations made
so far; unification intersects that set with the solutions of one more equation
and fails exactly when the intersection is empty; allocation keeps the solutions
and well-formedness.  Fresh frames depend only on the store's supply, which
unification does not change. -/
structure ExactStore (S : StoreAlgebra Term Store Op) where
  Valuation : Type
  solutions : Store → Set Valuation
  solves : Valuation → Term → Term → Prop
  WellFormed : Store → Prop
  Supply : Type
  supply : Store → Supply
  solves_comm : ∀ v t u, solves v t u ↔ solves v u t
  unify_some : ∀ {t u : Term} {σ σ' : Store}, WellFormed σ → S.unify t u σ = some σ' →
    solutions σ' = solutions σ ∩ {v | solves v t u}
  unify_none : ∀ {t u : Term} {σ : Store}, WellFormed σ → S.unify t u σ = none →
    solutions σ ∩ {v | solves v t u} = ∅
  unify_wellFormed : ∀ {t u : Term} {σ σ' : Store}, WellFormed σ →
    S.unify t u σ = some σ' → WellFormed σ'
  unify_supply : ∀ {t u : Term} {σ σ' : Store}, S.unify t u σ = some σ' →
    supply σ' = supply σ
  fresh_wellFormed : ∀ {σ : Store} (k : ℕ), WellFormed σ → WellFormed (S.fresh σ k).2
  fresh_solutions : ∀ (σ : Store) (k : ℕ), solutions (S.fresh σ k).2 = solutions σ
  fresh_supply : ∀ {σ σ' : Store} (k : ℕ), supply σ = supply σ' →
    (S.fresh σ k).1 = (S.fresh σ' k).1 ∧ supply (S.fresh σ k).2 = supply (S.fresh σ' k).2
  wellFormed_nonempty : ∀ {σ : Store}, WellFormed σ → (solutions σ).Nonempty

variable {S : StoreAlgebra Term Store Op} (X : ExactStore S)

namespace ExactStore

/-- Unification fails exactly when no solution of the store solves the
equation. -/
theorem unify_eq_none_iff {t u : Term} {σ : Store} (good : X.WellFormed σ) :
    S.unify t u σ = none ↔ X.solutions σ ∩ {v | X.solves v t u} = ∅ := by
  constructor
  · exact X.unify_none good
  · intro empty
    cases unified : S.unify t u σ with
    | none => rfl
    | some σ' =>
        obtain ⟨v, member⟩ := X.wellFormed_nonempty (X.unify_wellFormed good unified)
        rw [X.unify_some good unified, empty] at member
        exact absurd member (Set.notMem_empty v)

/-- Unifying an equation that every solution of the store already satisfies
succeeds and adds no constraint.  This is the binding a `let` repeats on the
output-first side after making it ahead. -/
theorem unify_entailed {t u : Term} {σ : Store} (good : X.WellFormed σ)
    (entailed : X.solutions σ ⊆ {v | X.solves v t u}) :
    ∃ σ', S.unify t u σ = some σ' ∧ X.solutions σ' = X.solutions σ := by
  cases unified : S.unify t u σ with
  | none =>
      have empty := X.unify_none good unified
      rw [Set.inter_eq_left.mpr entailed] at empty
      exact absurd empty (X.wellFormed_nonempty good).ne_empty
  | some σ' =>
      exact ⟨σ', rfl, by rw [X.unify_some good unified, Set.inter_eq_left.mpr entailed]⟩

end ExactStore

/-- Valuations solving every pair of two lists of the same length. -/
def solvesAll (ps as : List Term) : Set X.Valuation := {v | List.Forall₂ (X.solves v) ps as}

/-- `unifyAll` is exact: it intersects the solutions with those of every pair. -/
theorem unifyAll_exact :
    ∀ (ps as : List Term) (σ : Store), X.WellFormed σ →
      (∀ σ', unifyAll S ps as σ = some σ' →
        X.solutions σ' = X.solutions σ ∩ solvesAll X ps as ∧ X.WellFormed σ' ∧
          X.supply σ' = X.supply σ) ∧
      (unifyAll S ps as σ = none → X.solutions σ ∩ solvesAll X ps as = ∅)
  | [], [], σ, _ => by
      refine ⟨fun σ' accepted => ?_, fun rejected => by simp [unifyAll] at rejected⟩
      simp only [unifyAll, Option.some.injEq] at accepted
      subst accepted
      refine ⟨?_, by assumption, rfl⟩
      ext v
      simp [solvesAll]
  | p :: ps, a :: as, σ, good => by
      have pair : ∀ v, v ∈ solvesAll X (p :: ps) (a :: as) ↔
          X.solves v p a ∧ v ∈ solvesAll X ps as := by
        intro v
        simp [solvesAll]
      cases unified : S.unify p a σ with
      | none =>
          refine ⟨fun σ' accepted => by simp [unifyAll, unified] at accepted, fun _ => ?_⟩
          have empty := X.unify_none good unified
          ext v
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          intro inSol inAll
          have : v ∈ X.solutions σ ∩ {v | X.solves v p a} := ⟨inSol, ((pair v).mp inAll).1⟩
          rw [empty] at this
          exact this
      | some σ₁ =>
          have sols₁ := X.unify_some good unified
          have good₁ := X.unify_wellFormed good unified
          obtain ⟨accept, reject⟩ := unifyAll_exact ps as σ₁ good₁
          have step : unifyAll S (p :: ps) (a :: as) σ = unifyAll S ps as σ₁ := by
            simp [unifyAll, unified]
          have shape : X.solutions σ₁ ∩ solvesAll X ps as =
              X.solutions σ ∩ solvesAll X (p :: ps) (a :: as) := by
            ext v
            rw [sols₁]
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, pair]
            tauto
          refine ⟨fun σ' accepted => ?_, fun rejected => ?_⟩
          · rw [step] at accepted
            obtain ⟨sols', good', supply'⟩ := accept σ' accepted
            exact ⟨sols'.trans shape, good', supply'.trans (X.unify_supply unified)⟩
          · rw [step] at rejected
            rw [← shape]
            exact reject rejected
  | [], _ :: _, σ, _ => by
      refine ⟨fun σ' accepted => by simp [unifyAll] at accepted, fun _ => ?_⟩
      ext v
      simp [solvesAll]
  | _ :: _, [], σ, _ => by
      refine ⟨fun σ' accepted => by simp [unifyAll] at accepted, fun _ => ?_⟩
      ext v
      simp [solvesAll]

end Exact

/-! ## The correspondence -/

section Correspondence

variable {Term Store Rel Op : Type}
variable (L : TemplateLanguage Term) {S : StoreAlgebra Term Store Op} (X : ExactStore S)

/-- Valuations solving the bindings `E`, instantiated in `origin`. -/
def binds {k : Nat} (E : List (L.Tmpl k × L.Tmpl k)) (origin : Fin k → Term) : Set X.Valuation :=
  {v | ∀ e ∈ E, X.solves v (L.inst e.1 origin) (L.inst e.2 origin)}

/-- Valuations in which an exposed output meets a destination, when both exist. -/
def meets (exposed dest : Option Term) : Set X.Valuation :=
  {v | ∀ a d, exposed = some a → dest = some d → X.solves v a d}

/-- The equations one level of an output-at-return task still owes its
output-first counterpart: the bindings made ahead, and its exposed output
meeting its destination. -/
def pending {k : Nat} (E : List (L.Tmpl k × L.Tmpl k)) (origin : Fin k → Term)
    (code : Code L Rel Op k) (frame : Fin k → Term) (dest : Option Term) : Set X.Valuation :=
  binds L X E origin ∩ meets X (code.exposed.map fun x => L.inst x frame) dest

variable {L X}

theorem binds_nil {k : Nat} (origin : Fin k → Term) : binds L X [] origin = Set.univ := by
  ext v
  simp [binds]

theorem mem_binds_cons {k : Nat} {p v : L.Tmpl k} {E : List (L.Tmpl k × L.Tmpl k)}
    {origin : Fin k → Term} {w : X.Valuation} :
    w ∈ binds L X ((p, v) :: E) origin ↔
      X.solves w (L.inst p origin) (L.inst v origin) ∧ w ∈ binds L X E origin := by
  simp [binds]

theorem meets_none_left (dest : Option Term) : meets X none dest = Set.univ := by
  ext v
  simp [meets]

theorem meets_none_right (exposed : Option Term) : meets X exposed none = Set.univ := by
  ext v
  simp [meets]

theorem mem_meets_some {a d : Term} {w : X.Valuation} :
    w ∈ meets X (some a) (some d) ↔ X.solves w a d := by
  simp [meets]

theorem pending_ite {k : Nat} (E : List (L.Tmpl k × L.Tmpl k)) (origin frame : Fin k → Term)
    (op : Op) (args : List (L.Tmpl k)) (yes no : Code L Rel Op k) (dest : Option Term) :
    pending L X E origin (.ite op args yes no) frame dest = binds L X E origin := by
  simp [pending, Code.exposed, meets_none_left]

/-- The pending equations of a level do not depend on slots its code does not
read. -/
theorem pending_congr {k : Nat} (E : List (L.Tmpl k × L.Tmpl k)) (origin : Fin k → Term)
    (code : Code L Rel Op k) {frame frame' : Fin k → Term}
    (agree : ∀ i ∈ code.support L, frame i = frame' i) (dest : Option Term) :
    pending L X E origin code frame dest = pending L X E origin code frame' dest := by
  unfold pending
  congr 2
  cases exposed : code.exposed with
  | none => rfl
  | some x =>
      simp only [Option.map_some]
      rw [L.inst_congr x frame frame' fun i member =>
        agree i (Code.exposed_support code exposed member)]

/-- Exactness of meeting a destination. -/
theorem meet_exact {k : Nat} (frame : Fin k → Term) (code : Code L Rel Op k) (dest : Option Term)
    (σ : Store) (good : X.WellFormed σ) :
    (∀ σ', meet L S frame code dest σ = some σ' →
      X.solutions σ' = X.solutions σ ∩ meets X (code.exposed.map fun x => L.inst x frame) dest ∧
        X.WellFormed σ' ∧ X.supply σ' = X.supply σ) ∧
    (meet L S frame code dest σ = none →
      X.solutions σ ∩ meets X (code.exposed.map fun x => L.inst x frame) dest = ∅) := by
  unfold meet
  cases exposed : code.exposed with
  | none =>
      simp only [Option.map_none, meets_none_left, Set.inter_univ]
      exact ⟨fun σ' accepted => by cases accepted; exact ⟨rfl, good, rfl⟩,
        fun rejected => by cases rejected⟩
  | some x =>
      cases dest with
      | none =>
          simp only [Option.map_some, meets_none_right, Set.inter_univ]
          exact ⟨fun σ' accepted => by cases accepted; exact ⟨rfl, good, rfl⟩,
            fun rejected => by cases rejected⟩
      | some d =>
          simp only [Option.map_some]
          have same : meets X (some (L.inst x frame)) (some d) =
              {v | X.solves v (L.inst x frame) d} := by
            ext v
            exact mem_meets_some
          rw [same]
          exact ⟨fun σ' accepted =>
              ⟨X.unify_some good accepted, X.unify_wellFormed good accepted,
                X.unify_supply accepted⟩,
            fun rejected => X.unify_none good rejected⟩

variable (L X) [Inhabited Term]

/-- The return stack of an output-at-return task and of its output-first
counterpart: the same resume sites and captured slots, bodies related by
`BindsAhead`, and each output-first frame holding the destination of the code
that resumes.  The index is the destination of the code running above, and the
set is the equations the frames' levels still owe. -/
inductive FramesRel : Option Term → List (ReturnFrame L Rel Op) → List (DestFrame L Rel Op) →
    Set X.Valuation → Prop
  | nil : FramesRel none [] [] Set.univ
  | cons {k : Nat} (p : L.Tmpl k) {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (captured : Fin k → Option Term) (origin : Fin k → Term) (dest : Option Term)
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
      (ahead : BindsAhead L E late early)
      (agrees : ∀ i ∈ late.support L, reconstruct captured i = origin i)
      (rest : FramesRel dest fs gs P) :
      FramesRel (some (L.inst p (reconstruct captured))) (⟨k, p, late, captured⟩ :: fs)
        (⟨⟨k, p, early, captured⟩, dest⟩ :: gs)
        (pending L X E origin late (reconstruct captured) dest ∩ P)

/-- A task of each machine that correspond: same code position up to bindings
made ahead, same frame and return sites, and an output-first store whose
solutions are the output-at-return store's intersected with every equation it
still owes. -/
inductive Related :
    Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) →
      Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) → Prop
  | mk {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (frame origin : Fin k → Term) (σA σF : Store) (dest : Option Term)
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
      (ahead : BindsAhead L E late early) (agrees : ∀ i ∈ late.support L, frame i = origin i)
      (frames : FramesRel L X dest fs gs P) (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
      (sols : X.solutions σF = X.solutions σA ∩ pending L X E origin late frame dest ∩ P)
      (keys : X.supply σF = X.supply σA) :
      Related ⟨(), ⟨k, late, frame, σA⟩, fs⟩ ⟨(), ⟨⟨k, early, frame, σF⟩, dest⟩, gs⟩

/-- An output-at-return task that can deliver no answer: it fails at once, or
the equations it still owes have no solution in its store. -/
inductive Doomed : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) → Prop
  | failing {k : Nat} (frame : Fin k → Term) (σ : Store) (fs : List (ReturnFrame L Rel Op)) :
      Doomed ⟨(), ⟨k, .fail, frame, σ⟩, fs⟩
  | unsatisfiable {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (frame origin : Fin k → Term) (σ : Store) (dest : Option Term)
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
      (ahead : BindsAhead L E late early) (agrees : ∀ i ∈ late.support L, frame i = origin i)
      (frames : FramesRel L X dest fs gs P) (good : X.WellFormed σ)
      (empty : X.solutions σ ∩ pending L X E origin late frame dest ∩ P = ∅) :
      Doomed ⟨(), ⟨k, late, frame, σ⟩, fs⟩

/-- Corresponding answers: the same value, and consistent stores with the same
solutions and supply. -/
def SameAnswer (a b : Unit × Answer Term Store) : Prop :=
  a.2.1 = b.2.1 ∧ X.solutions a.2.2 = X.solutions b.2.2 ∧ X.supply a.2.2 = X.supply b.2.2 ∧
    X.WellFormed a.2.2 ∧ X.WellFormed b.2.2

/-- A reading of the store that no consistent refinement of `σ` changes. -/
def Stable {α : Type} (σ : Store) (read : Store → α) : Prop :=
  ∀ σ', X.WellFormed σ' → X.solutions σ' ⊆ X.solutions σ → X.supply σ' = X.supply σ →
    read σ' = read σ

/-- Every test and primitive the local work of a body evaluates, up to its next
call, return or failure, is stable in the store it sees. -/
inductive ModedCode {k : Nat} (frame : Fin k → Term) : Store → Code L Rel Op k → Prop
  | ret (σ : Store) (t : L.Tmpl k) : ModedCode frame σ (.ret t)
  | fail (σ : Store) : ModedCode frame σ .fail
  | letCall (σ : Store) (p : L.Tmpl k) (rel : Rel) (args : List (L.Tmpl k))
      (body : Code L Rel Op k) : ModedCode frame σ (.letCall p rel args body)
  | tail (σ : Store) (rel : Rel) (args : List (L.Tmpl k)) : ModedCode frame σ (.tail rel args)
  | letPrim (σ : Store) (p : L.Tmpl k) (op : Op) (args : List (L.Tmpl k))
      (body : Code L Rel Op k)
      (stable : Stable X σ (S.prim op (instArgs L args frame)))
      (next : ∀ v σ', S.prim op (instArgs L args frame) σ = some v →
        S.unify (L.inst p frame) v σ = some σ' → ModedCode frame σ' body) :
      ModedCode frame σ (.letPrim p op args body)
  | bind (σ : Store) (p v : L.Tmpl k) (body : Code L Rel Op k)
      (next : ∀ σ', S.unify (L.inst p frame) (L.inst v frame) σ = some σ' →
        ModedCode frame σ' body) :
      ModedCode frame σ (.bind p v body)
  | ite (σ : Store) (op : Op) (args : List (L.Tmpl k)) (yes no : Code L Rel Op k)
      (stable : Stable X σ (S.test op (instArgs L args frame)))
      (onYes : S.test op (instArgs L args frame) σ = some true → ModedCode frame σ yes)
      (onNo : S.test op (instArgs L args frame) σ = some false → ModedCode frame σ no) :
      ModedCode frame σ (.ite op args yes no)

/-- A task whose local work evaluates only stable tests and primitives. -/
def Moded (t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)) : Prop :=
  ModedCode L X t.control.frame t.control.store t.control.code

omit [Inhabited Term] in
/-- When no test or primitive reads the bindings of a consistent store, every
task is moded. -/
theorem moded_of_stable
    (stable : ∀ op args (σ : Store), Stable X σ (S.test op args) ∧ Stable X σ (S.prim op args))
    (t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)) : Moded L X t := by
  rcases t with ⟨_, ⟨k, code, frame, σ⟩, _⟩
  show ModedCode L X frame σ code
  induction code generalizing σ with
  | ret t => exact .ret σ t
  | fail => exact .fail σ
  | letCall p rel args body _ => exact .letCall σ p rel args body
  | tail rel args => exact .tail σ rel args
  | letPrim p op args body ih =>
      exact .letPrim σ p op args body (stable op _ σ).2 fun _ σ' _ _ => ih σ'
  | bind p v body ih => exact .bind σ p v body fun σ' _ => ih σ'
  | ite op args yes no ihYes ihNo =>
      exact .ite σ op args yes no (stable op _ σ).1 (fun _ => ihYes σ) (fun _ => ihNo σ)

/-- An instruction reached by an output-at-return task whose owed equations have
no solution. -/
inductive DoomedInstruction (dest : Option Term) (P : Set X.Valuation) :
    Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store) → Prop
  | ret (v : Term) (σ : Store) (good : X.WellFormed σ)
      (empty : X.solutions σ ∩ meets X (some v) dest ∩ P = ∅) :
      DoomedInstruction dest P (.ret (v, σ))
  | fail : DoomedInstruction dest P .fail
  | call (rel : Rel) (args : List Term) (σ : Store) {k : Nat} (p : L.Tmpl k)
      {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (captured : Fin k → Option Term) (origin : Fin k → Term)
      (ahead : BindsAhead L E late early)
      (agrees : ∀ i ∈ late.support L, reconstruct captured i = origin i) (good : X.WellFormed σ)
      (empty : X.solutions σ ∩ pending L X E origin late (reconstruct captured) dest ∩ P = ∅) :
      DoomedInstruction dest P (.call (rel, args, σ) ⟨k, p, late, captured⟩)
  | tail (rel : Rel) (args : List Term) (σ : Store) (good : X.WellFormed σ)
      (empty : X.solutions σ ∩ P = ∅) : DoomedInstruction dest P (.tail (rel, args, σ))

/-- The instructions reached by corresponding controls. -/
inductive InspectRelated (dest : Option Term) (P : Set X.Valuation) :
    Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store) →
      Instruction (DestCall Term Store Rel) (DestFrame L Rel Op) (Answer Term Store) → Prop
  | ret (v : Term) (σA σF : Store) (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
      (sols : X.solutions σF = X.solutions σA ∩ meets X (some v) dest ∩ P)
      (keys : X.supply σF = X.supply σA) :
      InspectRelated dest P (.ret (v, σA)) (.ret (v, σF))
  | fail : InspectRelated dest P .fail .fail
  | call (rel : Rel) (args : List Term) (σA σF : Store) {k : Nat} (p : L.Tmpl k)
      {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (captured : Fin k → Option Term) (origin : Fin k → Term)
      (ahead : BindsAhead L E late early)
      (agrees : ∀ i ∈ late.support L, reconstruct captured i = origin i)
      (goodA : X.WellFormed σA) (goodF : X.WellFormed σF)
      (sols : X.solutions σF =
        X.solutions σA ∩ pending L X E origin late (reconstruct captured) dest ∩ P)
      (keys : X.supply σF = X.supply σA) :
      InspectRelated dest P (.call (rel, args, σA) ⟨k, p, late, captured⟩)
        (.call (rel, args, σF, some (L.inst p (reconstruct captured)))
          ⟨⟨k, p, early, captured⟩, dest⟩)
  | tail (rel : Rel) (args : List Term) (σA σF : Store) (goodA : X.WellFormed σA)
      (goodF : X.WellFormed σF)
      (sols : X.solutions σF = X.solutions σA ∩ P) (keys : X.supply σF = X.supply σA) :
      InspectRelated dest P (.tail (rel, args, σA)) (.tail (rel, args, σF, dest))
  | doomed
      {instruction : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
      (doomed : DoomedInstruction L X dest P instruction) : InspectRelated dest P instruction .fail

/-! ### Local work -/

variable {L X}

/-- A resume frame captures what its site reads, so the level it resumes owes
the same equations as the control that built it. -/
theorem pending_capture {k : Nat} (E : List (L.Tmpl k × L.Tmpl k)) (origin frame : Fin k → Term)
    (p : L.Tmpl k) (rel : Rel) (args : List (L.Tmpl k)) (late : Code L Rel Op k)
    (dest : Option Term) :
    pending L X E origin late (reconstruct (capture frame (frameSupport L p late))) dest =
      pending L X E origin (.letCall p rel args late) frame dest := by
  rw [pending_congr E origin late (frame' := frame) (fun i member =>
    reconstruct_capture frame _ i (by simp [frameSupport, member])) dest]
  rfl

theorem agrees_capture {k : Nat} {origin frame : Fin k → Term} {p : L.Tmpl k} {rel : Rel}
    {args : List (L.Tmpl k)} {late : Code L Rel Op k}
    (agrees : ∀ i ∈ (Code.letCall p rel args late).support L, frame i = origin i) :
    ∀ i ∈ late.support L, reconstruct (capture frame (frameSupport L p late)) i = origin i :=
  fun i member => (reconstruct_capture frame _ i (by simp [frameSupport, member])).trans
    (agrees i (by simp [Code.support, member]))

/-- An output-at-return control whose owed equations have no solution reaches a
doomed instruction. -/
theorem inspect_doomed {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
    (ahead : BindsAhead L E late early) (frame origin : Fin k → Term) (dest : Option Term)
    (P : Set X.Valuation) :
    ∀ σ : Store, X.WellFormed σ → (∀ i ∈ late.support L, frame i = origin i) →
      X.solutions σ ∩ pending L X E origin late frame dest ∩ P = ∅ →
      DoomedInstruction L X dest P (inspectCode L S frame σ late) := by
  induction ahead with
  | ret t =>
      intro σ good _ empty
      refine .ret _ σ good ?_
      simpa [pending, binds_nil, Code.exposed] using empty
  | fail E => intro σ _ _ _; exact .fail
  | tail rel args =>
      intro σ good _ empty
      refine .tail rel _ σ good ?_
      simpa [pending, binds_nil, Code.exposed, meets_none_left] using empty
  | @letCall E late early p rel args h _ =>
      intro σ good agrees empty
      exact .call rel _ σ p (capture frame (frameSupport L p late)) origin h
        (agrees_capture agrees) good
        (by rw [pending_capture E origin frame p rel args late dest]; exact empty)
  | @letPrim E late early p op args h ih =>
      intro σ good agrees empty
      simp only [inspectCode]
      split
      · exact .fail
      · rename_i v _
        split
        · rename_i σ' unified
          refine ih σ' (X.unify_wellFormed good unified)
            (fun i member => agrees i (by simp [Code.support, member])) ?_
          refine Set.subset_eq_empty ?_ empty
          rintro w ⟨⟨inSol, inPending⟩, inP⟩
          rw [X.unify_some good unified] at inSol
          exact ⟨⟨inSol.1, inPending⟩, inP⟩
        · exact .fail
  | @bind E late early p v h ih =>
      intro σ good agrees empty
      simp only [inspectCode]
      split
      · rename_i σ' unified
        refine ih σ' (X.unify_wellFormed good unified)
          (fun i member => agrees i (by simp [Code.support, member])) ?_
        refine Set.subset_eq_empty ?_ empty
        rintro w ⟨⟨inSol, inPending⟩, inP⟩
        rw [X.unify_some good unified] at inSol
        exact ⟨⟨inSol.1, inPending⟩, inP⟩
      · exact .fail
  | @settle E late early p v h ih =>
      intro σ good agrees empty
      simp only [inspectCode]
      split
      · rename_i σ' unified
        refine ih σ' (X.unify_wellFormed good unified)
          (fun i member => agrees i (by simp [Code.support, member])) ?_
        refine Set.subset_eq_empty ?_ empty
        rintro w ⟨⟨inSol, inBinds, inMeets⟩, inP⟩
        rw [X.unify_some good unified] at inSol
        have sameP : L.inst p frame = L.inst p origin :=
          L.inst_congr p frame origin fun i member => agrees i (by simp [Code.support, member])
        have sameV : L.inst v frame = L.inst v origin :=
          L.inst_congr v frame origin fun i member => agrees i (by simp [Code.support, member])
        refine ⟨⟨inSol.1, mem_binds_cons.mpr ⟨?_, inBinds⟩, inMeets⟩, inP⟩
        have := inSol.2
        simp only [Set.mem_ofPred_eq, sameP, sameV] at this
        exact this
      · exact .fail
  | @ahead E late early p v h inside ih =>
      intro σ good agrees empty
      refine ih σ good agrees (Set.subset_eq_empty ?_ empty)
      rintro w ⟨⟨inSol, inBinds, inMeets⟩, inP⟩
      exact ⟨⟨inSol, (mem_binds_cons.mp inBinds).2, inMeets⟩, inP⟩
  | @ite E yes yes' no no' op args hYes hNo ihYes ihNo =>
      intro σ good agrees empty
      rw [pending_ite] at empty
      simp only [inspectCode]
      split
      · refine ihYes σ good (fun i member => agrees i (by simp [Code.support, member])) ?_
        refine Set.subset_eq_empty ?_ empty
        rintro w ⟨⟨inSol, inBinds, _⟩, inP⟩
        exact ⟨⟨inSol, inBinds⟩, inP⟩
      · refine ihNo σ good (fun i member => agrees i (by simp [Code.support, member])) ?_
        refine Set.subset_eq_empty ?_ empty
        rintro w ⟨⟨inSol, inBinds, _⟩, inP⟩
        exact ⟨⟨inSol, inBinds⟩, inP⟩
      · exact .fail

/-- Corresponding controls reach corresponding instructions, or the
output-first control fails and the output-at-return one reaches a doomed
instruction. -/
theorem inspect_related {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
    (ahead : BindsAhead L E late early) (frame origin : Fin k → Term) (dest : Option Term)
    (P : Set X.Valuation) :
    ∀ σA σF : Store, X.WellFormed σA → X.WellFormed σF →
      (∀ i ∈ late.support L, frame i = origin i) →
      X.solutions σF = X.solutions σA ∩ pending L X E origin late frame dest ∩ P →
      X.supply σF = X.supply σA → ModedCode L X frame σA late →
      InspectRelated L X dest P (inspectCode L S frame σA late)
        (inspectOut L S frame dest σF early) := by
  induction ahead with
  | ret t =>
      intro σA σF goodA goodF _ sols keys _
      refine .ret _ σA σF goodA goodF ?_ keys
      simpa [pending, binds_nil, Code.exposed] using sols
  | fail E => intro _ _ _ _ _ _ _ _; exact .fail
  | tail rel args =>
      intro σA σF goodA goodF _ sols keys _
      refine .tail rel _ σA σF goodA goodF ?_ keys
      simpa [pending, binds_nil, Code.exposed, meets_none_left] using sols
  | @letCall E late early p rel args h _ =>
      intro σA σF goodA goodF agrees sols keys _
      have supports : frameSupport L p early = frameSupport L p late := by
        simp [frameSupport, h.support_eq]
      have destination :
          L.inst p frame = L.inst p (reconstruct (capture frame (frameSupport L p late))) :=
        L.inst_congr p _ _ fun i member =>
          (reconstruct_capture frame _ i (by simp [frameSupport, member])).symm
      simp only [inspectCode, inspectOut, supports, destination]
      exact .call rel _ σA σF p (capture frame (frameSupport L p late)) origin h
        (agrees_capture agrees) goodA goodF
        (by rw [pending_capture E origin frame p rel args late dest]; exact sols) keys
  | @letPrim E late early p op args h ih =>
      intro σA σF goodA goodF agrees sols keys moded
      cases moded with
      | letPrim _ _ _ _ _ stable next =>
      have below : X.solutions σF ⊆ X.solutions σA := by
        rw [sols]
        exact fun w member => member.1.1
      have samePrim := stable σF goodF below keys
      have agrees' : ∀ i ∈ late.support L, frame i = origin i :=
        fun i member => agrees i (by simp [Code.support, member])
      cases primResult : S.prim op (instArgs L args frame) σA with
      | none =>
          simp only [inspectCode, inspectOut, samePrim, primResult]
          exact .fail
      | some v =>
          cases unifiedA : S.unify (L.inst p frame) v σA with
          | none =>
              have unifiedF : S.unify (L.inst p frame) v σF = none := by
                rw [X.unify_eq_none_iff goodF]
                exact Set.subset_eq_empty (Set.inter_subset_inter_left _ below)
                  (X.unify_none goodA unifiedA)
              simp only [inspectCode, inspectOut, samePrim, primResult, unifiedA, unifiedF]
              exact .fail
          | some σA' =>
              have solsA := X.unify_some goodA unifiedA
              have goodA' := X.unify_wellFormed goodA unifiedA
              have shape : X.solutions σF ∩ {w | X.solves w (L.inst p frame) v} =
                  X.solutions σA' ∩ pending L X E origin late frame dest ∩ P := by
                rw [sols, solsA]
                ext w
                simp only [pending, Code.exposed, Set.mem_inter_iff, Set.mem_ofPred_eq]
                tauto
              cases unifiedF : S.unify (L.inst p frame) v σF with
              | none =>
                  simp only [inspectCode, inspectOut, samePrim, primResult, unifiedA, unifiedF]
                  exact .doomed (inspect_doomed h frame origin dest P σA' goodA' agrees'
                    (by rw [← shape]; exact X.unify_none goodF unifiedF))
              | some σF' =>
                  simp only [inspectCode, inspectOut, samePrim, primResult, unifiedA, unifiedF]
                  exact ih σA' σF' goodA' (X.unify_wellFormed goodF unifiedF) agrees'
                    (by rw [X.unify_some goodF unifiedF, shape])
                    ((X.unify_supply unifiedF).trans (keys.trans (X.unify_supply unifiedA).symm))
                    (next v σA' primResult unifiedA)
  | @bind E late early p v h ih =>
      intro σA σF goodA goodF agrees sols keys moded
      cases moded with
      | bind _ _ _ _ next =>
      have below : X.solutions σF ⊆ X.solutions σA := by
        rw [sols]
        exact fun w member => member.1.1
      have agrees' : ∀ i ∈ late.support L, frame i = origin i :=
        fun i member => agrees i (by simp [Code.support, member])
      cases unifiedA : S.unify (L.inst p frame) (L.inst v frame) σA with
      | none =>
          have unifiedF : S.unify (L.inst p frame) (L.inst v frame) σF = none := by
            rw [X.unify_eq_none_iff goodF]
            exact Set.subset_eq_empty (Set.inter_subset_inter_left _ below)
              (X.unify_none goodA unifiedA)
          simp only [inspectCode, inspectOut, unifiedA, unifiedF]
          exact .fail
      | some σA' =>
          have solsA := X.unify_some goodA unifiedA
          have goodA' := X.unify_wellFormed goodA unifiedA
          have shape : X.solutions σF ∩ {w | X.solves w (L.inst p frame) (L.inst v frame)} =
              X.solutions σA' ∩ pending L X E origin late frame dest ∩ P := by
            rw [sols, solsA]
            ext w
            simp only [pending, Code.exposed, Set.mem_inter_iff, Set.mem_ofPred_eq]
            tauto
          cases unifiedF : S.unify (L.inst p frame) (L.inst v frame) σF with
          | none =>
              simp only [inspectCode, inspectOut, unifiedA, unifiedF]
              exact .doomed (inspect_doomed h frame origin dest P σA' goodA' agrees'
                (by rw [← shape]; exact X.unify_none goodF unifiedF))
          | some σF' =>
              simp only [inspectCode, inspectOut, unifiedA, unifiedF]
              exact ih σA' σF' goodA' (X.unify_wellFormed goodF unifiedF) agrees'
                (by rw [X.unify_some goodF unifiedF, shape])
                ((X.unify_supply unifiedF).trans (keys.trans (X.unify_supply unifiedA).symm))
                (next σA' unifiedA)
  | @settle E late early p v h ih =>
      intro σA σF goodA goodF agrees sols keys moded
      cases moded with
      | bind _ _ _ _ next =>
      have sameP : L.inst p frame = L.inst p origin :=
        L.inst_congr p frame origin fun i member => agrees i (by simp [Code.support, member])
      have sameV : L.inst v frame = L.inst v origin :=
        L.inst_congr v frame origin fun i member => agrees i (by simp [Code.support, member])
      have agrees' : ∀ i ∈ late.support L, frame i = origin i :=
        fun i member => agrees i (by simp [Code.support, member])
      -- the output-first store already solves the binding
      have solved : X.solutions σF ⊆ {w | X.solves w (L.inst p frame) (L.inst v frame)} := by
        rw [sols]
        rintro w ⟨⟨_, inBinds, _⟩, _⟩
        have := (mem_binds_cons.mp inBinds).1
        simpa [sameP, sameV] using this
      have nonemptyF := X.wellFormed_nonempty goodF
      obtain ⟨σF', unifiedF, solsF⟩ := X.unify_entailed goodF solved
      have unifiedA : ∃ σA', S.unify (L.inst p frame) (L.inst v frame) σA = some σA' := by
        cases result : S.unify (L.inst p frame) (L.inst v frame) σA with
        | none =>
            have empty := X.unify_none goodA result
            obtain ⟨w, member⟩ := nonemptyF
            have inA : w ∈ X.solutions σA := by rw [sols] at member; exact member.1.1
            have : w ∈ X.solutions σA ∩ {w | X.solves w (L.inst p frame) (L.inst v frame)} :=
              ⟨inA, solved member⟩
            rw [empty] at this
            exact absurd this (Set.notMem_empty w)
        | some σA' => exact ⟨σA', rfl⟩
      obtain ⟨σA', unifiedA⟩ := unifiedA
      simp only [inspectCode, inspectOut, unifiedA, unifiedF]
      have solsA := X.unify_some goodA unifiedA
      have goodA' := X.unify_wellFormed goodA unifiedA
      refine ih σA' σF' goodA' (X.unify_wellFormed goodF unifiedF) agrees' ?_
        ((X.unify_supply unifiedF).trans (keys.trans (X.unify_supply unifiedA).symm))
        (next σA' unifiedA)
      · rw [solsF, sols, solsA]
        ext w
        simp only [pending, Code.exposed, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_binds_cons,
          ← sameP, ← sameV]
        tauto
  | @ahead E late early p v h inside ih =>
      intro σA σF goodA goodF agrees sols keys moded
      have sameP : L.inst p frame = L.inst p origin :=
        L.inst_congr p frame origin fun i member => agrees i (inside (by simp [member]))
      have sameV : L.inst v frame = L.inst v origin :=
        L.inst_congr v frame origin fun i member => agrees i (inside (by simp [member]))
      have shape : X.solutions σF ∩ {w | X.solves w (L.inst p frame) (L.inst v frame)} =
          X.solutions σA ∩ pending L X ((p, v) :: E) origin late frame dest ∩ P := by
        rw [sols]
        ext w
        simp only [pending, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_binds_cons, ← sameP, ← sameV]
        tauto
      cases unifiedF : S.unify (L.inst p frame) (L.inst v frame) σF with
      | none =>
          simp only [inspectOut, unifiedF]
          exact .doomed (inspect_doomed h frame origin dest P σA goodA agrees
            (by rw [← shape]; exact X.unify_none goodF unifiedF))
      | some σF' =>
          simp only [inspectOut, unifiedF]
          exact ih σA σF' goodA (X.unify_wellFormed goodF unifiedF) agrees
            (by rw [X.unify_some goodF unifiedF, shape]) ((X.unify_supply unifiedF).trans keys)
            moded
  | @ite E yes yes' no no' op args hYes hNo ihYes ihNo =>
      intro σA σF goodA goodF agrees sols keys moded
      cases moded with
      | ite _ _ _ _ _ stable onYes onNo =>
      rw [pending_ite] at sols
      have below : X.solutions σF ⊆ X.solutions σA := by
        rw [sols]
        exact fun w member => member.1.1
      have sameTest := stable σF goodF below keys
      -- a branch first meets its exposed output with the destination
      have branch : ∀ {late early : Code L Rel Op k}, BindsAhead L E late early →
          (∀ σ', meet L S frame early dest σF = some σ' →
            X.solutions σ' = X.solutions σA ∩ pending L X E origin late frame dest ∩ P ∧
              X.WellFormed σ' ∧
              X.supply σ' = X.supply σA) ∧
          (meet L S frame early dest σF = none →
            X.solutions σA ∩ pending L X E origin late frame dest ∩ P = ∅) := by
        intro late early hb
        obtain ⟨accept, reject⟩ := meet_exact (L := L) (X := X) frame early dest σF goodF
        rw [hb.exposed_eq] at accept reject
        refine ⟨fun σ' met => ?_, fun met => ?_⟩
        · obtain ⟨sols', good', supply'⟩ := accept σ' met
          refine ⟨?_, good', supply'.trans keys⟩
          rw [sols', sols]
          ext w
          simp only [pending, Set.mem_inter_iff]
          tauto
        · have empty := reject met
          rw [sols] at empty
          refine Set.subset_eq_empty ?_ empty
          rintro w ⟨⟨inSol, inBinds, inMeets⟩, inP⟩
          exact ⟨⟨⟨inSol, inBinds⟩, inP⟩, inMeets⟩
      have agreesYes : ∀ i ∈ yes.support L, frame i = origin i :=
        fun i member => agrees i (by simp [Code.support, member])
      have agreesNo : ∀ i ∈ no.support L, frame i = origin i :=
        fun i member => agrees i (by simp [Code.support, member])
      cases testResult : S.test op (instArgs L args frame) σA with
      | none =>
          simp only [inspectCode, inspectOut, sameTest, testResult]
          exact .fail
      | some b =>
          cases b with
          | true =>
              obtain ⟨accept, reject⟩ := branch hYes
              cases met : meet L S frame yes' dest σF with
              | none =>
                  simp only [inspectCode, inspectOut, sameTest, testResult, met]
                  exact .doomed
                    (inspect_doomed hYes frame origin dest P σA goodA agreesYes (reject met))
              | some σ' =>
                  simp only [inspectCode, inspectOut, sameTest, testResult, met]
                  obtain ⟨sols', good', supply'⟩ := accept σ' met
                  exact ihYes σA σ' goodA good' agreesYes sols' supply' (onYes testResult)
          | false =>
              obtain ⟨accept, reject⟩ := branch hNo
              cases met : meet L S frame no' dest σF with
              | none =>
                  simp only [inspectCode, inspectOut, sameTest, testResult, met]
                  exact .doomed
                    (inspect_doomed hNo frame origin dest P σA goodA agreesNo (reject met))
              | some σ' =>
                  simp only [inspectCode, inspectOut, sameTest, testResult, met]
                  obtain ⟨sols', good', supply'⟩ := accept σ' met
                  exact ihNo σA σ' goodA good' agreesNo sols' supply' (onNo testResult)

end Correspondence

/-! ## Programs and runs -/

section Runs

variable {Term Store Rel Op : Type}
variable (L : TemplateLanguage Term) {S : StoreAlgebra Term Store Op} (X : ExactStore S)

/-- Equations with the same head and slots whose bodies are related by
`BindsAhead []`. -/
inductive EquationBindsAhead : Equation L Rel Op → Equation L Rel Op → Prop
  | mk {k : Nat} (params : List (L.Tmpl k)) {late early : Code L Rel Op k}
      (ahead : BindsAhead L [] late early) :
      EquationBindsAhead ⟨k, params, late⟩ ⟨k, params, early⟩

/-- Programs with the same equations, in the same order, whose bodies are
related by `BindsAhead []`. -/
def ProgramBindsAhead (PA PF : EqProgram L Rel Op) : Prop :=
  List.Forall₂ (fun a f => a.1 = f.1 ∧ EquationBindsAhead L a.2 f.2) PA PF

variable {L}

/-- Output-first normalization of a source program binds ahead of its
normalization. -/
theorem programBindsAhead_normalize (P : SProgram L Rel Op) :
    ProgramBindsAhead L (SProgram.normalize L P) (SProgram.normalizeFirst L P) := by
  induction P with
  | nil => exact .nil
  | cons entry rest ih =>
      exact .cons ⟨rfl, .mk entry.2.params (bindsAhead_norm entry.2.rhs)⟩ ih

theorem exists_of_forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a : α}, a ∈ l → ∃ b ∈ l', R a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons (b := b) head rest, a, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨b, List.mem_cons_self, head⟩
      · obtain ⟨b', member', related⟩ := exists_of_forall₂_mem rest member
        exact ⟨b', List.mem_cons_of_mem _ member', related⟩

theorem embeds_filterMap {α β γ δ : Type} {R : γ → δ → Prop} {D : γ → Prop}
    {Q : α → β → Prop} (fA : α → Option γ) (fF : β → Option δ)
    (pair : ∀ a b, Q a b → (fA a = none → fF b = none) ∧
      ∀ x, fA a = some x → (fF b = none ∧ D x) ∨ ∃ y, fF b = some y ∧ R x y) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ Q l l' →
      Embeds R D (l.filterMap fA) (l'.filterMap fF)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons q rest => by
      obtain ⟨onNone, onSome⟩ := pair a b q
      have tail := embeds_filterMap fA fF pair rest
      cases hA : fA a with
      | none =>
          rw [List.filterMap_cons_none hA, List.filterMap_cons_none (onNone hA)]
          exact tail
      | some x =>
          rcases onSome x hA with ⟨hF, d⟩ | ⟨y, hF, r⟩
          · rw [List.filterMap_cons_some hA, List.filterMap_cons_none hF]
            exact .drop d tail
          · rw [List.filterMap_cons_some hA, List.filterMap_cons_some hF]
            exact .keep r tail

variable [DecidableEq Rel]

theorem ProgramBindsAhead.equations {PA PF : EqProgram L Rel Op}
    (aligned : ProgramBindsAhead L PA PF) (rel : Rel) :
    List.Forall₂ (EquationBindsAhead L) (PA.equations rel) (PF.equations rel) := by
  induction aligned with
  | nil => exact .nil
  | @cons a f restA restF head _ ih =>
      obtain ⟨same, equation⟩ := head
      simp only [EqProgram.equations] at ih ⊢
      by_cases hit : a.1 = rel
      · have hitF : f.1 = rel := same ▸ hit
        simp only [List.filter_cons, hit, hitF, decide_true, ↓reduceIte, List.map_cons]
        exact .cons equation ih
      · have missF : ¬ f.1 = rel := same ▸ hit
        simp only [List.filter_cons, hit, missF, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih

variable [Inhabited Term]

/-- The activations of one call on the two sides: an equation the
output-at-return side activates is activated by the output-first side and the
two tasks correspond, or it is not and the output-at-return task is doomed. -/
theorem activations_embed {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    (rel : Rel) (args : List Term) (σA σF : Store) (goodA : X.WellFormed σA)
    (goodF : X.WellFormed σF)
    (keys : X.supply σF = X.supply σA) (dest : Option Term) {fs : List (ReturnFrame L Rel Op)}
    {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P)
    (sols : X.solutions σF = X.solutions σA ∩ P) :
    Embeds (Related L X) (Doomed L X)
      ((activate L S PA (rel, args, σA)).map fun a =>
        (⟨(), ⟨a.slots, a.code, a.frame, a.store⟩, fs⟩ :
          Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
      ((activateOut L S PF (rel, args, σF, dest)).map fun a =>
        (⟨(), a, gs⟩ : Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))) := by
  simp only [activate, activateOut, List.map_filterMap]
  refine embeds_filterMap _ _ ?_ (aligned.equations rel)
  intro eA eF related
  cases related with
  | @mk k params late early ahead =>
  obtain ⟨sameFrame, sameKey⟩ := X.fresh_supply k keys.symm
  obtain ⟨acceptA, rejectA⟩ :=
    unifyAll_exact X (instArgs L params (S.fresh σA k).1) args (S.fresh σA k).2
      (X.fresh_wellFormed k goodA)
  obtain ⟨acceptF, rejectF⟩ :=
    unifyAll_exact X (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2
      (X.fresh_wellFormed k goodF)
  simp only [← sameFrame, Option.map_map]
  refine ⟨fun noneA => ?_, fun task someA => ?_⟩
  · -- the output-first head fails too
    rw [Option.map_eq_none_iff] at noneA
    have empty := rejectA noneA
    have noneF : unifyAll S (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2 = none := by
      cases unified : unifyAll S (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2 with
      | none => rfl
      | some σ' =>
          obtain ⟨sols', good', _⟩ := acceptF σ' unified
          obtain ⟨w, member⟩ := X.wellFormed_nonempty good'
          rw [sols', X.fresh_solutions, sols] at member
          have : w ∈ X.solutions (S.fresh σA k).2 ∩
              solvesAll X (instArgs L params (S.fresh σA k).1) args := by
            rw [X.fresh_solutions]
            exact ⟨member.1.1, member.2⟩
          rw [empty] at this
          exact absurd this (Set.notMem_empty w)
    simp [noneF]
  · rw [Option.map_eq_some_iff] at someA
    obtain ⟨σA', unifiedA, rfl⟩ := someA
    obtain ⟨solsA, goodA', keyA⟩ := acceptA σA' unifiedA
    rw [X.fresh_solutions] at solsA
    have doomedA :
        X.solutions σA' ∩ pending L X [] (S.fresh σA k).1 late (S.fresh σA k).1 dest ∩ P = ∅ →
        Doomed L X ⟨(), ⟨k, late, (S.fresh σA k).1, σA'⟩, fs⟩ :=
      Doomed.unsatisfiable _ _ σA' dest ahead (fun _ _ => rfl) frames goodA'
    have shape :
        X.solutions (S.fresh σF k).2 ∩ solvesAll X (instArgs L params (S.fresh σA k).1) args =
        X.solutions σA' ∩ P := by
      rw [X.fresh_solutions, sols, solsA]
      ext w
      simp only [Set.mem_inter_iff]
      tauto
    cases unifiedF : unifyAll S (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2 with
    | none =>
        refine .inl ⟨by simp, doomedA ?_⟩
        refine Set.subset_eq_empty ?_ ((shape ▸ rejectF unifiedF))
        rintro w ⟨⟨inSol, _⟩, inP⟩
        exact ⟨inSol, inP⟩
    | some σF' =>
        obtain ⟨solsF, goodF', keyF⟩ := acceptF σF' unifiedF
        obtain ⟨acceptM, rejectM⟩ :=
          meet_exact (L := L) (X := X) (S.fresh σA k).1 early dest σF' goodF'
        rw [ahead.exposed_eq] at acceptM rejectM
        cases met : meet L S (S.fresh σA k).1 early dest σF' with
        | none =>
            refine .inl ⟨by simp [met], doomedA ?_⟩
            have empty := rejectM met
            rw [solsF, shape] at empty
            refine Set.subset_eq_empty ?_ empty
            rintro w ⟨⟨inSol, _, inMeets⟩, inP⟩
            exact ⟨⟨inSol, inP⟩, inMeets⟩
        | some σF'' =>
            obtain ⟨solsM, goodM, keyM⟩ := acceptM σF'' met
            refine .inr ⟨⟨(), ⟨⟨k, early, (S.fresh σA k).1, σF''⟩, dest⟩, gs⟩,
              by simp [met], ?_⟩
            refine Related.mk _ _ σA' σF'' dest ahead (fun _ _ => rfl) frames goodA' goodM ?_ ?_
            · rw [solsM, solsF, shape]
              ext w
              simp only [pending, binds_nil, Set.mem_inter_iff, Set.mem_univ, true_and]
              tauto
            · rw [keyM, keyF, keyA]
              exact sameKey.symm

/-- The activations of a call whose owed equations have no solution are all
doomed. -/
theorem activations_doomed {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    (rel : Rel) (args : List Term) (σ : Store) (good : X.WellFormed σ) (dest : Option Term)
    {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
    (frames : FramesRel L X dest fs gs P) (empty : X.solutions σ ∩ P = ∅) :
    ∀ t ∈ (activate L S PA (rel, args, σ)).map (fun a =>
        (⟨(), ⟨a.slots, a.code, a.frame, a.store⟩, fs⟩ :
          Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))), Doomed L X t := by
  intro t member
  simp only [List.mem_map, activate, List.mem_filterMap, Option.map_eq_some_iff] at member
  obtain ⟨_, ⟨e, eMember, σ', unified, rfl⟩, rfl⟩ := member
  obtain ⟨e', _, related⟩ := exists_of_forall₂_mem (aligned.equations rel) eMember
  cases related with
  | @mk k params late early ahead =>
  obtain ⟨sols', good', _⟩ :=
    (unifyAll_exact X _ args (S.fresh σ k).2 (X.fresh_wellFormed k good)).1 σ' unified
  rw [X.fresh_solutions] at sols'
  refine Doomed.unsatisfiable _ _ σ' dest ahead (fun _ _ => rfl) frames good' ?_
  refine Set.subset_eq_empty ?_ empty
  rintro w ⟨⟨inSol, _⟩, inP⟩
  rw [sols'] at inSol
  exact ⟨inSol.1, inP⟩

/-- A doomed instruction yields only doomed tasks and no answer. -/
theorem successors_doomed {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P)
    {instruction : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
    (doomed : DoomedInstruction L X dest P instruction) :
    (∀ t ∈ (expandWith (compiled L S PA) () fs instruction).1, Doomed L X t) ∧
      (expandWith (compiled L S PA) () fs instruction).2 = [] := by
  cases doomed with
  | ret v σ good empty =>
      cases frames with
      | nil =>
          simp only [meets_none_right, Set.inter_univ] at empty
          exact absurd empty (X.wellFormed_nonempty good).ne_empty
      | @cons k p E late early captured origin dest' fs' gs' P' ahead agrees rest =>
          refine ⟨fun t member => ?_, rfl⟩
          simp only [expandWith, List.mem_singleton] at member
          subst member
          change Doomed L X ⟨(), resumeControl L S ⟨k, p, late, captured⟩ (v, σ), fs'⟩
          simp only [resumeControl]
          cases unified : S.unify (L.inst p (reconstruct captured)) v σ with
          | none => exact .failing _ _ _
          | some σ' =>
              refine Doomed.unsatisfiable _ origin σ' dest' ahead agrees rest
                (X.unify_wellFormed good unified) ?_
              refine Set.subset_eq_empty ?_ empty
              rintro w ⟨⟨inSol, inPending⟩, inP⟩
              rw [X.unify_some good unified] at inSol
              refine ⟨⟨inSol.1, ?_⟩, inPending, inP⟩
              intro a d hA hD
              simp only [Option.some.injEq] at hA hD
              subst hA hD
              exact (X.solves_comm _ _ _).mp inSol.2
  | fail => exact ⟨fun _ member => by simp [expandWith] at member, rfl⟩
  | call rel args σ p captured origin ahead agrees good empty =>
      refine ⟨fun t member => ?_, rfl⟩
      simp only [expandWith, compiled, List.map_map] at member
      exact activations_doomed X aligned rel args σ good _
        (.cons p captured origin dest ahead agrees frames) (by rw [← Set.inter_assoc]; exact empty)
        t (by simpa [Function.comp_def] using member)
  | tail rel args σ good empty =>
      refine ⟨fun t member => ?_, rfl⟩
      simp only [expandWith, compiled, List.map_map] at member
      exact activations_doomed X aligned rel args σ good _ frames empty t
        (by simpa [Function.comp_def] using member)

/-- Corresponding instructions yield corresponding tasks and answers. -/
theorem successors_related {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P)
    {iA : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
    {iF : Instruction (DestCall Term Store Rel) (DestFrame L Rel Op) (Answer Term Store)}
    (related : InspectRelated L X dest P iA iF) :
    Embeds (Related L X) (Doomed L X) (expandWith (compiled L S PA) () fs iA).1
        (expandWith (outputFirst L S PF) () gs iF).1 ∧
      List.Forall₂ (SameAnswer X) (expandWith (compiled L S PA) () fs iA).2
        (expandWith (outputFirst L S PF) () gs iF).2 := by
  cases related with
  | ret v σA σF goodA goodF sols keys =>
      cases frames with
      | nil =>
          simp only [meets_none_right, Set.inter_univ] at sols
          exact ⟨.nil, .cons ⟨rfl, sols.symm, keys.symm, goodA, goodF⟩ .nil⟩
      | @cons k p E late early captured origin dest' fs' gs' P' ahead agrees rest =>
          refine ⟨?_, .nil⟩
          simp only [expandWith]
          change Embeds (Related L X) (Doomed L X)
            [⟨(), resumeControl L S ⟨k, p, late, captured⟩ (v, σA), fs'⟩]
            [⟨(), ⟨⟨k, early, reconstruct captured, σF⟩, dest'⟩, gs'⟩]
          simp only [resumeControl]
          have solved : X.solutions σF ⊆
              X.solutions σA ∩ {w | X.solves w (L.inst p (reconstruct captured)) v} := by
            rw [sols]
            rintro w ⟨⟨inSol, inMeets⟩, _⟩
            exact ⟨inSol, (X.solves_comm _ _ _).mp (inMeets v _ rfl rfl)⟩
          cases unified : S.unify (L.inst p (reconstruct captured)) v σA with
          | none =>
              have empty := X.unify_none goodA unified
              exact absurd (Set.subset_eq_empty solved empty) (X.wellFormed_nonempty goodF).ne_empty
          | some σA' =>
              refine .keep (Related.mk _ origin σA' σF dest' ahead agrees rest
                (X.unify_wellFormed goodA unified) goodF ?_
                (keys.trans (X.unify_supply unified).symm)) .nil
              rw [sols, X.unify_some goodA unified]
              ext w
              simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
              constructor
              · rintro ⟨⟨inSol, inMeets⟩, inPending, inP⟩
                exact ⟨⟨⟨inSol, (X.solves_comm _ _ _).mp (inMeets v _ rfl rfl)⟩, inPending⟩, inP⟩
              · rintro ⟨⟨⟨inSol, inSat⟩, inPending⟩, inP⟩
                refine ⟨⟨inSol, ?_⟩, inPending, inP⟩
                intro a d hA hD
                simp only [Option.some.injEq] at hA hD
                subst hA hD
                exact (X.solves_comm _ _ _).mp inSat
  | fail => exact ⟨.nil, .nil⟩
  | call rel args σA σF p captured origin ahead agrees goodA goodF sols keys =>
      refine ⟨?_, .nil⟩
      simp only [expandWith, compiled, outputFirst, List.map_map]
      have embeds := activations_embed X aligned rel args σA σF goodA goodF keys _
        (.cons p captured origin dest ahead agrees frames) (by rw [sols, Set.inter_assoc])
      simpa [Function.comp_def] using embeds
  | tail rel args σA σF goodA goodF sols keys =>
      refine ⟨?_, .nil⟩
      simp only [expandWith, compiled, outputFirst, List.map_map]
      have embeds := activations_embed X aligned rel args σA σF goodA goodF keys _ frames sols
      simpa [Function.comp_def] using embeds
  | doomed d =>
      obtain ⟨all, none⟩ := successors_doomed X aligned frames d
      refine ⟨Embeds.of_forall all, ?_⟩
      rw [none]
      exact .nil

theorem expand_related {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {tA : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    {tF : Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op)}
    (related : Related L X tA tF) (moded : Moded L X tA) :
    Embeds (Related L X) (Doomed L X) (expand (compiled L S PA) tA).1
        (expand (outputFirst L S PF) tF).1 ∧
      List.Forall₂ (SameAnswer X) (expand (compiled L S PA) tA).2
        (expand (outputFirst L S PF) tF).2 := by
  cases related with
  | mk frame origin σA σF dest ahead agrees frames goodA goodF sols keys =>
      exact successors_related X aligned frames
        (inspect_related ahead frame origin dest _ σA σF goodA goodF agrees sols keys moded)

theorem expand_doomed {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)} (doomed : Doomed L X t) :
    (∀ t' ∈ (expand (compiled L S PA) t).1, Doomed L X t') ∧
      (expand (compiled L S PA) t).2 = [] := by
  cases doomed with
  | failing frame σ fs => exact ⟨fun _ member => by simp [expand, compiled, inspectCode,
      expandWith] at member, rfl⟩
  | unsatisfiable frame origin σ dest ahead agrees frames good empty =>
      exact successors_doomed X aligned frames
        (inspect_doomed ahead frame origin dest _ σ good agrees empty)

/-- **Output first refines output at return.**  For programs related by
`ProgramBindsAhead`, from corresponding states, and on a moded output-at-return
run: after `n` output-at-return steps there are `n' ≤ n` output-first steps
after which the states still correspond. -/
theorem outputFirst_simulates {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m sA).frontier, Moded L X t)
    (n : ℕ) :
    ∃ n' ≤ n, Simulates (Related L X) (Doomed L X) (SameAnswer X)
      (repeats (step (compiled L S PA)) n sA) (repeats (step (outputFirst L S PF)) n' sF) :=
  simulates_repeats _ _ (Moded L X) (fun _ _ related m => expand_related X aligned related m)
    (fun _ doomed => expand_doomed X aligned doomed) n sA sF start (fun m _ => moded m)

/-- **The prefix law.**  Every answer list the output-at-return machine has
delivered within `n` steps, the output-first machine has delivered within some
`n' ≤ n` steps, answer for answer. -/
theorem outputFirst_answers {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m sA).frontier, Moded L X t)
    (n : ℕ) :
    ∃ n' ≤ n, List.Forall₂ (SameAnswer X) (repeats (step (compiled L S PA)) n sA).emitted
      (repeats (step (outputFirst L S PF)) n' sF).emitted :=
  let ⟨n', le, sim⟩ := outputFirst_simulates X aligned start moded n
  ⟨n', le, sim.2⟩

/-- **At least as defined.**  After `n` output-at-return steps, the delivered
answers correspond to a prefix of what the output-first machine has delivered
after any `m ≥ n` steps. -/
theorem outputFirst_at_least_as_defined {PA PF : EqProgram L Rel Op}
    (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m sA).frontier, Moded L X t)
    {n m : ℕ} (le : n ≤ m) :
    ∃ answers, answers <+: (repeats (step (outputFirst L S PF)) m sF).emitted ∧
      List.Forall₂ (SameAnswer X) (repeats (step (compiled L S PA)) n sA).emitted answers :=
  let ⟨n', le', same⟩ := outputFirst_answers X aligned start moded n
  ⟨_, emitted_repeats_prefix _ n' m sF (le'.trans le), same⟩

/-- **Termination.**  When the output-at-return run exhausts its frontier within
`n` steps, the output-first run exhausts its own within `n' ≤ n` steps, having
delivered the same ordered answers. -/
theorem outputFirst_terminates {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)}
    {sF : State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m sA).frontier, Moded L X t)
    (n : ℕ) (done : (repeats (step (compiled L S PA)) n sA).frontier = []) :
    ∃ n' ≤ n, (repeats (step (outputFirst L S PF)) n' sF).frontier = [] ∧
      List.Forall₂ (SameAnswer X) (repeats (step (compiled L S PA)) n sA).emitted
        (repeats (step (outputFirst L S PF)) n' sF).emitted := by
  obtain ⟨n', le, embeds, answers⟩ := outputFirst_simulates X aligned start moded n
  rw [done] at embeds
  exact ⟨n', le, embeds.eq_nil, answers⟩

/-! ### Initial states -/

variable (L)

/-- A query run as a control with no caller: typically a call whose pattern is
the query's destination, followed by the answer to report. -/
def queryState {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store) :=
  ⟨[⟨(), ⟨k, code, frame, σ⟩, []⟩], []⟩

/-- The same query in the output-first machine. -/
def queryStateOut {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    State Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) (Answer Term Store) :=
  ⟨[⟨(), ⟨⟨k, code, frame, σ⟩, none⟩, []⟩], []⟩

variable {L}

omit [DecidableEq Rel] in
theorem simulates_query {k : Nat} {late early : Code L Rel Op k}
    (ahead : BindsAhead L [] late early) (frame : Fin k → Term) (σ : Store)
    (good : X.WellFormed σ) :
    Simulates (Related L X) (Doomed L X) (SameAnswer X) (queryState L late frame σ)
      (queryStateOut L early frame σ) :=
  ⟨.keep (Related.mk frame frame σ σ none ahead (fun _ _ => rfl) .nil good good
    (by simp [pending, binds_nil, meets_none_right]) rfl) .nil, .nil⟩

theorem simulates_initial {PA PF : EqProgram L Rel Op} (aligned : ProgramBindsAhead L PA PF)
    (c : Call Term Store Rel) (good : X.WellFormed c.2.2) :
    Simulates (Related L X) (Doomed L X) (SameAnswer X) (initial L S PA c)
      (initialOut L S PF c) := by
  rcases c with ⟨rel, args, σ⟩
  refine ⟨?_, .nil⟩
  have embeds := activations_embed X aligned rel args σ σ good good rfl none .nil
    (by simp)
  simpa [initial, initialOut] using embeds

/-- For a source program, the output-first machine on its output-first
normalization refines the defunctionalized machine on its normalization, from a
query control. -/
theorem source_outputFirst_answers (P : SProgram L Rel Op) {k : Nat} (query : Code L Rel Op k)
    (frame : Fin k → Term) (σ : Store) (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S (SProgram.normalize L P))) m
      (queryState L query frame σ)).frontier, Moded L X t) (n : ℕ) :
    ∃ n' ≤ n, List.Forall₂ (SameAnswer X)
      (repeats (step (compiled L S (SProgram.normalize L P))) n
        (queryState L query frame σ)).emitted
      (repeats (step (outputFirst L S (SProgram.normalizeFirst L P))) n'
        (queryStateOut L query frame σ)).emitted :=
  outputFirst_answers X (programBindsAhead_normalize P)
    (simulates_query X (BindsAhead.refl query) frame σ good) moded n

end Runs

/-! ## The substitution store -/

section SubstitutionStore

open Mettapedia.Logic.LP
open CompiledTwoSidedHeadProgram

universe r

variable {σ : LPSignature.{0, 0, r, 0}}
variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars) {Op : Type}
  (prim : Op → List (Term σ) → Subst σ × ℕ → Option (Term σ))
  (test : Op → List (Term σ) → Subst σ × ℕ → Option Bool)

/-- Unifying in an idempotent store: the substitutions absorbing the result are
those absorbing the store and solving the equation, the result is idempotent,
and the supply is unchanged.  This is where most generality
(`unifyTotal_mgu`) and relevance (`unifyTotal_relevantIdempotent`) enter. -/
theorem substitution_unify_some {t u : Term σ} {θ : Subst σ} {n : ℕ} {store : Subst σ × ℕ}
    (idempotent : θ.Absorbs θ)
    (accepted : (substitutionStore name prim test).unify t u (θ, n) = some store) :
    {δ : Subst σ | δ.Absorbs store.1} =
        {δ : Subst σ | δ.Absorbs θ} ∩ {δ | δ.applyTerm t = δ.applyTerm u} ∧
      store.1.Absorbs store.1 ∧ store.2 = n := by
  simp only [substitutionStore, Option.map_eq_some_iff] at accepted
  obtain ⟨μ, unified, rfl⟩ := accepted
  have relevant := unifyTotal_relevantIdempotent _ μ unified
  have solved := unifyTotal_sound _ μ unified (θ.applyTerm t, θ.applyTerm u) (by simp)
  refine ⟨?_, ?_, rfl⟩
  · ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro absorbs
      refine ⟨absorbs.trans (Subst.comp_absorbs idempotent), ?_⟩
      rw [← absorbs.applyTerm t, ← absorbs.applyTerm u, Subst.applyTerm_comp,
        Subst.applyTerm_comp]
      exact congrArg δ.applyTerm solved
    · rintro ⟨absorbsθ, same⟩
      have unifies : Unifies δ [(θ.applyTerm t, θ.applyTerm u)] := by
        intro equation member
        simp only [List.mem_singleton] at member
        subst member
        change δ.applyTerm (θ.applyTerm t) = δ.applyTerm (θ.applyTerm u)
        rw [absorbsθ.applyTerm, absorbsθ.applyTerm, same]
      exact (Subst.absorbs_of_moreGeneral relevant.absorbs
        (unifyTotal_mgu _ μ unified δ unifies)).comp absorbsθ
  · have pairFixed : ∀ x ∈ eqVars [(θ.applyTerm t, θ.applyTerm u)], θ x = .var x := by
      intro x memberX
      simp only [eqVars, Finset.union_empty, Finset.mem_union] at memberX
      rcases memberX with inT | inU
      · exact idempotent.var_fixed t x inT
      · exact idempotent.var_fixed u x inU
    refine Subst.comp_idempotent relevant.absorbs fun w => ?_
    apply Subst.applyTerm_eq_self
    intro x memberX
    rcases Finset.mem_union.mp (relevant.freeVars_applyTerm_subset _ memberX) with
      inRead | inPair
    · exact idempotent.var_fixed (.var w) x inRead
    · exact pairFixed x inPair

/-- Unification fails only when no substitution absorbing the store solves the
equation (`unifyTotal_none_iff_not_unifiable`). -/
theorem substitution_unify_none {t u : Term σ} {θ : Subst σ} {n : ℕ}
    (rejected : (substitutionStore name prim test).unify t u (θ, n) = none) :
    {δ : Subst σ | δ.Absorbs θ} ∩ {δ | δ.applyTerm t = δ.applyTerm u} = ∅ := by
  simp only [substitutionStore, Option.map_eq_none_iff] at rejected
  have notUnifiable := (unifyTotal_none_iff_not_unifiable _).mp rejected
  ext δ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro absorbsθ same
  refine notUnifiable ⟨δ, fun equation member => ?_⟩
  simp only [List.mem_singleton] at member
  subst member
  change δ.applyTerm (θ.applyTerm t) = δ.applyTerm (θ.applyTerm u)
  rw [absorbsθ.applyTerm, absorbsθ.applyTerm, same]

/-- **The substitution store is exact.**  A store denotes the substitutions
absorbing it (its instances, for an idempotent store), a well-formed store is an
idempotent one, the equation `t = u` holds in `δ` when `δ` sends both sides to
the same term, and the supply is the fresh-variable counter. -/
def substitutionExact : ExactStore (substitutionStore name prim test) where
  Valuation := Subst σ
  solutions store := {δ | δ.Absorbs store.1}
  solves δ t u := δ.applyTerm t = δ.applyTerm u
  WellFormed store := store.1.Absorbs store.1
  Supply := ℕ
  supply store := store.2
  solves_comm _ _ _ := eq_comm
  unify_some {t u store store'} good accepted := by
    rcases store with ⟨θ, n⟩
    exact (substitution_unify_some name prim test good accepted).1
  unify_none {t u store} _ rejected := by
    rcases store with ⟨θ, n⟩
    exact substitution_unify_none name prim test rejected
  unify_wellFormed {t u store store'} good accepted := by
    rcases store with ⟨θ, n⟩
    exact (substitution_unify_some name prim test good accepted).2.1
  unify_supply {t u store store'} accepted := by
    rcases store with ⟨θ, n⟩
    simp only [substitutionStore, Option.map_eq_some_iff] at accepted
    obtain ⟨μ, _, rfl⟩ := accepted
    rfl
  fresh_wellFormed _ good := good
  fresh_solutions _ _ := rfl
  fresh_supply k same := by
    simp only [substitutionStore] at same ⊢
    exact ⟨by rw [same], by rw [same]⟩
  wellFormed_nonempty {store} good := ⟨store.1, good⟩

/-- Corresponding answers over the substitution store: the same value, and
stores that are instances of each other. -/
theorem sameAnswer_instances {a b : Unit × Answer (Term σ) (Subst σ × ℕ)}
    (same : SameAnswer (substitutionExact name prim test) a b) :
    a.2.1 = b.2.1 ∧ b.2.2.1.Absorbs a.2.2.1 ∧ a.2.2.1.Absorbs b.2.2.1 := by
  obtain ⟨value, sols, _, goodA, goodB⟩ := same
  refine ⟨value, ?_, ?_⟩
  · have member : b.2.2.1 ∈ (substitutionExact name prim test).solutions b.2.2 := goodB
    rw [← sols] at member
    exact member
  · have member : a.2.2.1 ∈ (substitutionExact name prim test).solutions a.2.2 := goodA
    rw [sols] at member
    exact member

/-- **Answers up to renaming.**  Over the substitution store, corresponding
answers are variants: the output-first store and answer, read through it, are
the output-at-return ones with their variables renamed injectively. -/
theorem sameAnswer_variant (n : ℕ) {a b : Unit × Answer (Term σ) (Subst σ × ℕ)}
    (same : SameAnswer (substitutionExact name prim test) a b) :
    VariantOffSupply name n (a.2.2.1, fun _ : Unit => a.2.2.1.applyTerm a.2.1)
      (b.2.2.1, fun _ : Unit => b.2.2.1.applyTerm b.2.1) := by
  obtain ⟨value, forward, backward⟩ := sameAnswer_instances name prim test same
  refine variantOffSupply_of_instances name ⟨b.2.2.1, fun v _ => (forward v).symm, fun _ => ?_⟩
    ⟨a.2.2.1, fun v _ => (backward v).symm, fun _ => ?_⟩
  · change b.2.2.1.applyTerm b.2.1 = b.2.2.1.applyTerm (a.2.2.1.applyTerm a.2.1)
    rw [forward.applyTerm, value]
  · change a.2.2.1.applyTerm a.2.1 = a.2.2.1.applyTerm (b.2.2.1.applyTerm b.2.1)
    rw [backward.applyTerm, value]

/-- A reading of the substitution store through some terms is stable wherever
those terms read ground: every consistent refinement reads them the same.  So a
test or primitive whose arguments the store already determines, the moded
calls of logic programming, meets the stability `ModedCode` asks for. -/
theorem substitution_stable_of_ground {α : Type} (read : List (Term σ) → ℕ → α)
    (args : List (Term σ)) {θ : Subst σ} {n : ℕ}
    (ground : ∀ t ∈ args, (θ.applyTerm t).freeVars = ∅) :
    Stable (substitutionExact name prim test) (θ, n)
      (fun store => read (args.map store.1.applyTerm) store.2) := by
  intro store' good' below sameKey
  rcases store' with ⟨θ', n'⟩
  change n' = n at sameKey
  subst sameKey
  have absorbs : θ'.Absorbs θ := below good'
  have same : args.map θ'.applyTerm = args.map θ.applyTerm := by
    apply List.map_congr_left
    intro t member
    rw [← absorbs.applyTerm t]
    refine Subst.applyTerm_eq_self fun v occurs => ?_
    rw [ground t member] at occurs
    exact absurd occurs (Finset.notMem_empty v)
  simp only [same]

/-- Tests and primitives that do not read the bindings (they may read the
supply counter) make every task moded. -/
theorem substitution_moded {Rel : Type}
    (independent : ∀ op args (θ θ' : Subst σ) (n : ℕ),
      test op args (θ, n) = test op args (θ', n) ∧ prim op args (θ, n) = prim op args (θ', n))
    (t : Task Unit (Control (headTemplates σ) Rel Op (Subst σ × ℕ))
      (ReturnFrame (headTemplates σ) Rel Op)) :
    Moded (headTemplates σ) (substitutionExact name prim test) t := by
  refine moded_of_stable (headTemplates σ) (substitutionExact name prim test)
    (fun op args store => ⟨?_, ?_⟩) t
  · intro store' _ _ sameKey
    rcases store with ⟨θ, n⟩
    rcases store' with ⟨θ', n'⟩
    change n' = n at sameKey
    subst sameKey
    exact (independent op args θ' θ n').1
  · intro store' _ _ sameKey
    rcases store with ⟨θ, n⟩
    rcases store' with ⟨θ', n'⟩
    change n' = n at sameKey
    subst sameKey
    exact (independent op args θ' θ n').2

end SubstitutionStore

end Mettapedia.GSLT.LanguageDef.DestinationPassing
