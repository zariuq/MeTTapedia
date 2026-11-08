import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension

/-!
# Application and lexical binding on the step

* **Runs transfer** (`path_on_step`, `runs_on_step`): every source run is matched by a run of
  translated firings, and every translated run from a program's rows represents a source run.
* **Reachable sets are computed** (`reach`): the configurations reachable from a program, closed
  under `successors`, so claims about every run are kernel computations (`every_run`).
* **β up to administrative firings** (`beta_up_to_administration`): `app (lam b) (atom d)` reaches
  the body under the extended scope by four administrative steps and one β step, and on the step by
  a run of translated firings (`beta_on_step`). Control: an application of an atom is stuck, on the
  step too (`atom_application_stuck`).
* **Lexical shadowing** (`shadowing_inner`, `shadowing_outer`): an inner `let` shadows index `0`;
  the outer binding stays reachable at index `1`. Every run of each program halts at that value only.
* **No capture** (`no_capture`): `(λ. λ. var 1) z w` halts at `z` in every run, never at `w`, the
  captured answer; on the step every halted configuration represents `z` (`no_capture_on_step`).
* **Noninterference of independent bindings** (`firing_conservative`), from w9's
  `selected_conservative_of_closed_avoiding`: a translated firing at a fresh scope preserves every
  closed component of the knowledge that avoids its scope and its selected labels, with all
  possibilities, asks and refutations reading only that component (`firing_verdicts`).
  Positive control (`threads_noninterfere`): two programs started side by side; a firing of one
  preserves the other's bindings. The closure hypothesis is necessary: w9's
  `FirstOrderAliasBoundaryControls.raw_name_avoidance_does_not_establish_noninterference`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-! ## Runs transfer -/

/-- **Every source run from represented rows is matched by a run of translated firings.** -/
theorem path_on_step {W W' : Multiset Sx} (path : Relation.ReflTransGen Step W W') {C : Config} {n : ℕ}
    (rep : Represents C W n) :
    ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (C, n) q ∧ Represents q.1 W' q.2 := by
  rw [step_eq_rewrites] at path
  exact path_sound schema_wellFormed path rep

/-- **Every translated run from a program's rows represents a source run.** -/
theorem runs_on_step {l : List Sx} {q : Config × ℕ}
    (run : Relation.ReflTransGen (Translated schema) (initial l, 1) q) :
    ∃ W, Relation.ReflTransGen Step (l : Multiset Sx) W ∧ Represents q.1 W q.2 := by
  obtain ⟨W, path, rep⟩ := path_complete schema_wellFormed run (initial_represents l)
  rw [← step_eq_rewrites] at path
  exact ⟨W, path, rep⟩

/-! ## Computed reachable sets -/

/-- Add the successors not yet present, up to order. -/
def expand (S : List (List Sx)) : List (List Sx) :=
  S ++ (S.flatMap successors).filter fun l => !(S.any fun W => l.isPerm W)

/-- The configurations reached by `k` rounds of successors. -/
def reach : ℕ → List (List Sx) → List (List Sx)
  | 0, S => S
  | k + 1, S => reach k (expand S)

theorem subset_reach : ∀ (k : ℕ) (S : List (List Sx)), ∀ W ∈ S, W ∈ reach k S
  | 0, _, _, h => h
  | k + 1, S, W, h => subset_reach k (expand S) W (List.mem_append_left _ h)

/-- **Every run from a program stays in a closed computed set.** -/
theorem every_run {k : ℕ} {W₀ : List Sx} (closed : SuccessorClosed (reach k [W₀]) = true)
    {W : Multiset Sx} (path : Relation.ReflTransGen Step (W₀ : Multiset Sx) W) :
    ∃ W' ∈ reach k [W₀], W = (W' : Multiset Sx) :=
  reachable_closed closed (subset_reach k [W₀] W₀ (List.mem_singleton_self _)) path

theorem expand_reachable {W₀ : List Sx} {S : List (List Sx)}
    (reached : ∀ W ∈ S, Relation.ReflTransGen Step (W₀ : Multiset Sx) (W : Multiset Sx)) :
    ∀ W ∈ expand S, Relation.ReflTransGen Step (W₀ : Multiset Sx) (W : Multiset Sx) := by
  intro W mem
  rcases List.mem_append.mp mem with old | new
  · exact reached W old
  · obtain ⟨V, VIn, succ⟩ := List.mem_flatMap.mp (List.mem_filter.mp new).1
    exact (reached V VIn).tail (step_of_successor succ)

theorem reach_reachable {W₀ : List Sx} : ∀ (k : ℕ) (S : List (List Sx)),
    (∀ W ∈ S, Relation.ReflTransGen Step (W₀ : Multiset Sx) (W : Multiset Sx)) →
      ∀ W ∈ reach k S, Relation.ReflTransGen Step (W₀ : Multiset Sx) (W : Multiset Sx)
  | 0, _, reached => reached
  | k + 1, S, reached => reach_reachable k (expand S) (expand_reachable reached)

/-- The halted configurations of a list: those without successors. -/
def halted (S : List (List Sx)) : List (List Sx) := S.filter fun W => (successors W).isEmpty

/-- **The halted runs of a program, from a closed computed set**: each listed halted configuration
is reached, and every reachable configuration without a step is one of them. -/
theorem halted_runs {k : ℕ} {W₀ : List Sx} (closed : SuccessorClosed (reach k [W₀]) = true) :
    (∀ H ∈ halted (reach k [W₀]), Relation.ReflTransGen Step (W₀ : Multiset Sx) (H : Multiset Sx) ∧
        ∀ W', ¬ Step (H : Multiset Sx) W') ∧
      ∀ W, Relation.ReflTransGen Step (W₀ : Multiset Sx) W → (∀ W', ¬ Step W W') →
        ∃ H ∈ halted (reach k [W₀]), W = (H : Multiset Sx) := by
  refine ⟨fun H mem => ⟨?_, ?_⟩, fun W path stuck => ?_⟩
  · exact reach_reachable k [W₀] (fun W h => by rw [List.mem_singleton.mp h]) H (List.mem_filter.mp mem).1
  · have none := (List.mem_filter.mp mem).2
    exact stuck_of_successors (List.isEmpty_iff.mp none)
  · obtain ⟨W', mem, rfl⟩ := every_run closed path
    refine ⟨W', List.mem_filter.mpr ⟨mem, ?_⟩, rfl⟩
    cases h : successors W' with
    | nil => rfl
    | cons l _ => exact absurd (step_of_successor (h ▸ List.mem_cons_self)) (stuck _)

/-- **Halted runs on the step**: a translated run from the program's rows that has no further firing
represents one of the halted configurations. -/
theorem halted_on_step {k : ℕ} {W₀ : List Sx} (closed : SuccessorClosed (reach k [W₀]) = true) {q : Config × ℕ}
    (run : Relation.ReflTransGen (Translated schema) (initial W₀, 1) q)
    (stuck : ∀ q', ¬ Translated schema q q') :
    ∃ H ∈ halted (reach k [W₀]), Represents q.1 (H : Multiset Sx) q.2 := by
  obtain ⟨W, path, rep⟩ := runs_on_step run
  have halts : ∀ W', ¬ Step W W' := fun W' step => by
    obtain ⟨q', firing, -⟩ := step_sound rep step
    exact stuck q' firing
  obtain ⟨H, mem, rfl⟩ := (halted_runs closed).2 W path halts
  exact ⟨H, mem, rep⟩

/-! ## Atoms used by the controls -/

def ka : Sx := .sym 100
def kb : Sx := .sym 101
def kz : Sx := .sym 102
def kw : Sx := .sym 103
def ku : Sx := .sym 104

/-! ## β up to administrative firings -/

/-- **β up to administrative firings**: four administrative steps, then one β step. -/
theorem beta_up_to_administration (b d ρ κ : Sx) (W : Multiset Sx) :
    ∃ W₁ W₂ W₃ W₄ : Multiset Sx,
      Administrative (ev (app (lam b) (atom d)) ρ κ ::ₘ W) W₁ ∧ Administrative W₁ W₂ ∧
        Administrative W₂ W₃ ∧ Administrative W₃ W₄ ∧ Step W₄ (ev b (cons (atom d) ρ) κ ::ₘ W) :=
  ⟨_, _, _, _, .app (lam b) (atom d) ρ κ W, .lam b ρ (cons (appL (atom d) ρ) κ) W,
    .appL (clo b ρ) (atom d) ρ κ W, .atom d ρ (cons (appR (clo b ρ)) κ) W, .beta (atom d) b ρ κ W⟩

/-- **β on the step**: from any configuration representing the redex, a run of translated firings
reaches a configuration representing the contracted body. -/
theorem beta_on_step (b d ρ κ : Sx) (W : Multiset Sx) {C : Config} {n : ℕ}
    (rep : Represents C (ev (app (lam b) (atom d)) ρ κ ::ₘ W) n) :
    ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (C, n) q ∧
      Represents q.1 (ev b (cons (atom d) ρ) κ ::ₘ W) q.2 := by
  obtain ⟨_, _, _, _, s₁, s₂, s₃, s₄, s₅⟩ := beta_up_to_administration b d ρ κ W
  exact path_on_step (.tail (.tail (.tail (.tail (.single s₁.step) s₂.step) s₃.step) s₄.step) s₅) rep

/-- **β after the argument**: once the argument evaluates to a value in its frame, the application
reaches the body under the extended scope, by three administrative steps, the argument's own
steps and one β step. -/
theorem beta_after_argument {b a v ρ κ : Sx} {W : Multiset Sx}
    (argument : Relation.ReflTransGen Step (ev a ρ (cons (appR (clo b ρ)) κ) ::ₘ W)
      (ret v (cons (appR (clo b ρ)) κ) ::ₘ W)) :
    Relation.ReflTransGen Step (ev (app (lam b) a) ρ κ ::ₘ W) (ev b (cons v ρ) κ ::ₘ W) :=
  ((((Relation.ReflTransGen.single (Step.app (lam b) a ρ κ W)).tail
    (Step.lam b ρ (cons (appL a ρ) κ) W)).tail (Step.appL (clo b ρ) a ρ κ W)).trans argument).tail
      (Step.beta v b ρ κ W)

/-- **β after the argument, on the step.** -/
theorem beta_after_argument_on_step {b a v ρ κ : Sx} {W : Multiset Sx}
    (argument : Relation.ReflTransGen Step (ev a ρ (cons (appR (clo b ρ)) κ) ::ₘ W)
      (ret v (cons (appR (clo b ρ)) κ) ::ₘ W)) {C : Config} {n : ℕ}
    (rep : Represents C (ev (app (lam b) a) ρ κ ::ₘ W) n) :
    ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (C, n) q ∧
      Represents q.1 (ev b (cons v ρ) κ ::ₘ W) q.2 :=
  path_on_step (beta_after_argument argument) rep

/-- The application of an atom. -/
def atomApplication : Sx := ev (app (atom ka) (atom kb)) nil nil

/-- **Control: an application of a non-closure is stuck**, at the source and on the step. -/
theorem atom_application_stuck :
    Relation.ReflTransGen Step ({atomApplication} : Multiset Sx) {ret (atom kb) (cons (appR (atom ka)) nil)} ∧
      (∀ W', ¬ Step ({ret (atom kb) (cons (appR (atom ka)) nil)} : Multiset Sx) W') ∧
      ∀ {C : Config} {n : ℕ}, Represents C {ret (atom kb) (cons (appR (atom ka)) nil)} n →
        ∀ q, ¬ Translated schema (C, n) q := by
  have chain : Chained [[atomApplication], [ev (atom ka) nil (cons (appL (atom kb) nil) nil)],
      [ret (atom ka) (cons (appL (atom kb) nil) nil)], [ev (atom kb) nil (cons (appR (atom ka)) nil)],
      [ret (atom kb) (cons (appR (atom ka)) nil)]] = true := by decide
  have none : successors [ret (atom kb) (cons (appR (atom ka)) nil)] = [] := by decide
  exact ⟨chain_reaches chain, stuck_of_successors none,
    fun rep q => stuck_of_source rep (stuck_of_successors none) q⟩

/-! ## Lexical shadowing -/

/-- `let a in let b in var 0`. -/
def shadowInner : Sx := ev (let_ (atom ka) (let_ (atom kb) (var zero))) nil nil
/-- `let a in let b in var 1`. -/
def shadowOuter : Sx := ev (let_ (atom ka) (let_ (atom kb) (var (succ zero)))) nil nil

theorem shadowInner_closed : SuccessorClosed (reach 8 [[shadowInner]]) = true := by decide
theorem shadowOuter_closed : SuccessorClosed (reach 9 [[shadowOuter]]) = true := by decide

/-- **An inner binder shadows**: every run of `let a in let b in var 0` halts at `b`, and one does. -/
theorem shadowing_inner : halted (reach 8 [[shadowInner]]) = [[ret (atom kb) nil]] := by decide

/-- **The outer binding stays reachable**: every run of `let a in let b in var 1` halts at `a`. -/
theorem shadowing_outer : halted (reach 9 [[shadowOuter]]) = [[ret (atom ka) nil]] := by decide

/-! ## No capture -/

/-- `(λ. λ. var 1) z w`: the inner binder must not capture the outer argument. -/
def captureProgram : Sx := ev (app (app (lam (lam (var (succ zero)))) (atom kz)) (atom kw)) nil nil

theorem captureProgram_closed : SuccessorClosed (reach 13 [[captureProgram]]) = true := by decide

/-- **No capture**: one run halts at `z`; every halted run halts at `z`, never at the captured `w`. -/
theorem no_capture :
    halted (reach 13 [[captureProgram]]) = [[ret (atom kz) nil]] ∧
      Relation.ReflTransGen Step ({captureProgram} : Multiset Sx) {ret (atom kz) nil} ∧
      ∀ W, Relation.ReflTransGen Step ({captureProgram} : Multiset Sx) W →
        (∀ W', ¬ Step W W') → W = {ret (atom kz) nil} := by
  have halts : halted (reach 13 [[captureProgram]]) = [[ret (atom kz) nil]] := by decide
  obtain ⟨reached, all⟩ := halted_runs captureProgram_closed
  rw [halts] at reached all
  refine ⟨halts, (reached _ (List.mem_singleton_self _)).1, fun W path stuck => ?_⟩
  obtain ⟨H, mem, rfl⟩ := all W path stuck
  rw [List.mem_singleton.mp mem]
  rfl

/-- **No capture on the step**: a translated run from the program with no further firing represents
`z`. -/
theorem no_capture_on_step {q : Config × ℕ}
    (run : Relation.ReflTransGen (Translated schema) (initial [captureProgram], 1) q)
    (stuck : ∀ q', ¬ Translated schema q q') : Represents q.1 {ret (atom kz) nil} q.2 := by
  obtain ⟨H, mem, rep⟩ := halted_on_step captureProgram_closed run stuck
  have halts : halted (reach 13 [[captureProgram]]) = [[ret (atom kz) nil]] := by decide
  rw [halts, List.mem_singleton] at mem
  subst mem
  exact rep

/-! ## Noninterference of independent bindings -/

open FirstOrderConservativeExtension FirstOrderAskLocality

theorem added_firing (r : Schema) (n : ℕ) (taken read : List Occ) :
    GuardFreeProcessOrders.added Occ.label (r.rule n) (r.firing n taken read).selection =
      Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl

/-- **A translated firing preserves every closed component that avoids its scope and its selected
labels** (w9's conservative extension, on the step). -/
theorem firing_conservative {C : Config} {n : ℕ} {r : Schema} {taken read : List Occ}
    (valid : (r.firing n taken read).Valid A Occ.label C) (component : Set (ℕ × ℕ))
    (closed : FirstOrderAskLocality.Closed component C.equations) (fresh : ∀ v ∈ component, v.1 ≠ n)
    (apart : ∀ o ∈ taken ++ read, ∀ v ∈ o.label.freeVars, v ∉ component) :
    ConservativeOn component C.equations ((r.firing n taken read).result Occ.label C).equations := by
  refine selected_conservative_of_closed_avoiding component Occ.label (r.rule n)
    (r.firing n taken read).selection C valid.firing closed ?_
  intro e member v hv inside
  rw [added_firing] at member
  simp only [List.append_nil, List.mem_append] at member
  have side : ∀ {ps : List Pat} {os : List Occ}, (∀ o ∈ os, o ∈ taken ++ read) →
      e ∈ Selection.equations (T := Tm) Occ.label (ps.map (Pat.at n)) os → False := by
    intro ps os sub member
    obtain ⟨p', hp', o, ho, rfl⟩ := mem_equations member
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hp'
    rcases Finset.mem_union.mp hv with hv | hv
    · exact fresh v inside (at_scope n p v hv)
    · exact apart o (sub o ho) v hv inside
  rcases member with taken' | read'
  · exact side (fun o h => List.mem_append_left _ h) taken'
  · exact side (fun o h => List.mem_append_right _ h) read'

/-- **Every observation reading only the component keeps its possibility, ask and refutation.** -/
theorem firing_verdicts {C : Config} {n : ℕ} {r : Schema} {taken read : List Occ}
    (valid : (r.firing n taken read).Valid A Occ.label C) (component : Set (ℕ × ℕ))
    (closed : FirstOrderAskLocality.Closed component C.equations) (fresh : ∀ v ∈ component, v.1 ≠ n)
    (apart : ∀ o ∈ taken ++ read, ∀ v ∈ o.label.freeVars, v ∉ component)
    (observation : Mettapedia.Logic.LP.Subst rows → Prop) (reads : ReadsOnly component observation) :
    ((A.Entails ((r.firing n taken read).result Occ.label C).equations observation ↔
        A.Entails C.equations observation) ∧
      (A.Entails ((r.firing n taken read).result Occ.label C).equations (fun σ => ¬ observation σ) ↔
        A.Entails C.equations (fun σ => ¬ observation σ))) :=
  verdicts_iff (firing_conservative valid component closed fresh apart)
    (fun σ solved => by
      have := (Selection.Valid.refines valid.firing) σ solved
      exact this) observation reads

/-- The variables of one scope. -/
def scopeVars (m : ℕ) : Set (ℕ × ℕ) := {v | v.1 = m}

/-- **Positive control: two programs side by side do not interfere.** Start two rows `s₁, s₂`; fire
a schema `r₂` at scope `1` on the occurrence of `s₂`, then a schema `r₁` at scope `2` on the
occurrence of `s₁`. The second firing, if admitted, preserves every possibility of the first one's bindings;
the first firing need not even be admitted. -/
theorem threads_noninterfere (s₁ s₂ : Sx) (r₁ r₂ : Schema) (o₁ o₂ : Occ)
    (h₁ : o₁.label = embed s₁) (h₂ : o₂.label = embed s₂)
    (taken₂ read₂ taken₁ read₁ : List Occ)
    (only₂ : ∀ o ∈ taken₂ ++ read₂, o = o₂) (only₁ : ∀ o ∈ taken₁ ++ read₁, o = o₁)
    (C : Config) (empty : C.equations = [])
    (valid₁ : (r₁.firing 2 taken₁ read₁).Valid A Occ.label ((r₂.firing 1 taken₂ read₂).result Occ.label C)) :
    ConservativeOn (scopeVars 1) ((r₂.firing 1 taken₂ read₂).result Occ.label C).equations
      ((r₁.firing 2 taken₁ read₁).result Occ.label ((r₂.firing 1 taken₂ read₂).result Occ.label C)).equations := by
  have noVars : ∀ (s : Sx) (v : ℕ × ℕ), v ∉ (embed s).freeVars := fun s v hv => by
    have := embed_bounded 0 s v hv
    omega
  refine firing_conservative valid₁ (scopeVars 1) ?_ (fun v hv h => by
    have hv1 : v.1 = 1 := hv; omega) ?_
  · intro e member
    left
    have eqs : ((r₂.firing 1 taken₂ read₂).result Occ.label C).equations =
        C.equations ++ Selection.equations (T := Tm) Occ.label (r₂.take.map (Pat.at 1)) taken₂ ++
          Selection.equations (T := Tm) Occ.label (r₂.read.map (Pat.at 1)) read₂ ++ [] := rfl
    rw [eqs, empty] at member
    simp only [List.nil_append, List.append_nil, List.mem_append] at member
    have side : ∀ {ps : List Pat} {os : List Occ}, (∀ o ∈ os, o ∈ taken₂ ++ read₂) →
        e ∈ Selection.equations (T := Tm) Occ.label (ps.map (Pat.at 1)) os →
          ∀ v ∈ FirstOrderAskLocality.equationSupport e, v ∈ scopeVars 1 := by
      intro ps os sub member v hv
      obtain ⟨p', hp', o, ho, rfl⟩ := mem_equations member
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hp'
      rcases Finset.mem_union.mp hv with hv | hv
      · exact at_scope 1 p v hv
      · rw [only₂ o (sub o ho), h₂] at hv
        exact absurd hv (noVars s₂ v)
    rcases member with taken' | read'
    · exact side (fun o h => List.mem_append_left _ h) taken'
    · exact side (fun o h => List.mem_append_right _ h) read'
  · intro o ho v hv
    rw [only₁ o ho, h₁] at hv
    exact absurd hv (noVars s₁ v)

#print axioms path_on_step
#print axioms runs_on_step
#print axioms every_run
#print axioms halted_runs
#print axioms halted_on_step
#print axioms beta_up_to_administration
#print axioms beta_on_step
#print axioms beta_after_argument
#print axioms beta_after_argument_on_step
#print axioms atom_application_stuck
#print axioms shadowing_inner
#print axioms shadowing_outer
#print axioms no_capture
#print axioms no_capture_on_step
#print axioms firing_conservative
#print axioms firing_verdicts
#print axioms threads_noninterfere

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
