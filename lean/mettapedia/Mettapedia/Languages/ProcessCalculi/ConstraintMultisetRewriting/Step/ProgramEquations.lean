import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquationsOpen

/-!
# Definitions as pattern equations, matched by two-way unification

A definition is a list of **equations** `(= lhs rhs)` with pattern variables; several may share a
head. A thread evaluating a call `t` matches it against **every** equation of the program
(`EqStep`): the equation is renamed apart into the fresh scope `n`, the call is unified with the
left-hand side, and for a most general unifier `θ` the thread continues with the right-hand side
under `θ`, while `θ` binds the caller's variables in every row. So a call may contain variables that
the equation's patterns bind, and each matching equation gives one branch.

* **Reference semantics** (`EqStep`): an inductive relation over the equations themselves.
* **Compilation** (`compile`, `compiled`): one schema per equation, taking the call occurrence and
  making the instantiated right-hand side. The compiled schemas present the reference semantics
  exactly on tagged rows (`eqStep_iff`), rule by rule.
* **Adequacy** (`equations_execution`, `eqStep_sound`, `eqFiring_complete`): through the open-row
  adequacy of `ProgramEquationsOpen`, reference runs and runs of the ordinary step correspond in both
  directions; unification is done by the step's own equation store.
* **The answer multiset is exact** (`answers_exact`): from a represented configuration, the
  admitted firings on a call occurrence, one candidate per equation in program order, are in
  bijection with the program's matching equations, and each result represents that equation's answer
  (`answers`): no branch is lost and none is duplicated. A firing on the call is admitted exactly
  when its equation's left-hand side unifies with the call (`call_valid_iff`).
* **A call matching no equation has no firing** (`stuck_iff`): it stays as it is. It is not an
  error: the configuration is unchanged and consistent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen

/-! ## Tagged rows -/

/-- A row or expression with a constant tag at its head. -/
def tagged (k : ℕ) (t : Tm) : Tm := node (.const k) t

/-- The pattern of a tagged term. -/
def ptag (k : ℕ) (p : Pat) : Pat := .cell (.sym k) p

theorem ptag_at (k : ℕ) (p : Pat) (n : ℕ) : (ptag k p).at n = tagged k (p.at n) := rfl

theorem apply_tagged (σ : Subst rows) (k : ℕ) (t : Tm) :
    σ.applyTerm (tagged k t) = tagged k (σ.applyTerm t) := by
  rw [tagged, apply_node]
  rfl

theorem tagged_inj {k k' : ℕ} {s s' : Tm} : tagged k s = tagged k' s' ↔ k = k' ∧ s = s' := by
  rw [tagged, tagged, node_inj, Term.const.injEq]

theorem freeVars_tagged (k : ℕ) (t : Tm) : (tagged k t).freeVars = t.freeVars := by
  ext x
  rw [tagged, mem_freeVars_node]
  simp [Term.freeVars]

/-- A thread evaluating an expression. -/
def thread (t : Tm) : Tm := tagged 40 t

/-- Every row carries a constant tag. -/
def Tagged (t : Tm) : Prop := ∃ k s, t = tagged k s

theorem tagged_tagged (k : ℕ) (s : Tm) : Tagged (tagged k s) := ⟨k, s, rfl⟩

theorem Tagged.apply {t : Tm} (h : Tagged t) (σ : Subst rows) : Tagged (σ.applyTerm t) := by
  obtain ⟨k, s, rfl⟩ := h
  rw [apply_tagged]
  exact tagged_tagged k _

theorem unifies_single (δ : Subst rows) (s t : Tm) :
    Unifies δ [(s, t)] ↔ δ.applyTerm s = δ.applyTerm t := by
  simp [Unifies]

theorem unifies_tagged_iff (δ : Subst rows) (k : ℕ) (a b : Tm) :
    Unifies δ [(tagged k a, tagged k b)] ↔ Unifies δ [(a, b)] := by
  rw [unifies_single, unifies_single, apply_tagged, apply_tagged, tagged_inj]
  simp

theorem isMGU_tagged_iff {k : ℕ} {a b : Tm} {θ : Subst rows} :
    IsMGU [(tagged k a, tagged k b)] θ ↔ IsMGU [(a, b)] θ := by
  have vars : eqVars [(tagged k a, tagged k b)] = eqVars [(a, b)] := by
    simp only [eqVars, freeVars_tagged]
  constructor
  · intro mgu
    exact mgu.congr (fun δ => unifies_tagged_iff δ k a b) vars
  · intro mgu
    exact mgu.congr (fun δ => (unifies_tagged_iff δ k a b).symm) vars.symm

/-! ## Equations and their compiled schemas -/

/-- An equation `(= lhs rhs)`: a call pattern and its right-hand side. -/
structure Equation where
  lhs : Pat
  rhs : Pat
  deriving DecidableEq

/-- A program: equations in order; several may share a head. -/
abbrev Program := List Equation

/-- **The compiled schema of an equation**: take the call occurrence, make the instantiated
right-hand side. -/
def compile (e : Equation) : Schema := ⟨[ptag 40 e.lhs], [], [ptag 40 e.rhs]⟩

/-- The compiled program: one schema per equation. -/
def compiled (prog : Program) (j : Fin prog.length) : Schema := compile (prog.get j)

theorem compiled_single (prog : Program) (j : Fin prog.length) :
    (compiled prog j).read.length ≤ 1 := by
  simp [compiled, compile]

/-! ## The reference semantics -/

/-- **The reference semantics of pattern equations.** A thread evaluating `t`, and an equation of
the program renamed apart into the fresh scope `n`: for a most general unifier `θ` of the call with
the left-hand side, the thread continues with the right-hand side under `θ`, and `θ` binds the
caller's variables in every row. -/
inductive EqStep (prog : Program) : Multiset Tm × ℕ → Multiset Tm × ℕ → Prop
  | call (j : Fin prog.length) (t : Tm) (F : Multiset Tm) (n : ℕ) (θ : Subst rows)
      (mgu : IsMGU [((prog.get j).lhs.at n, t)] θ) :
      EqStep prog (thread t ::ₘ F, n)
        (thread (θ.applyTerm ((prog.get j).rhs.at n)) ::ₘ F.map θ.applyTerm, n + 1)

theorem compiled_rows (e : Equation) (n : ℕ) (θ : Subst rows) (F : Multiset Tm) :
    (((compile e).make.map fun q => θ.applyTerm (q.at n) : List Tm) : Multiset Tm) +
        (((([] : List Tm).map θ.applyTerm : List Tm) : Multiset Tm) + F.map θ.applyTerm) =
      thread (θ.applyTerm (e.rhs.at n)) ::ₘ F.map θ.applyTerm := by
  simp only [compile, List.map_cons, List.map_nil, ptag_at, apply_tagged, Multiset.coe_nil,
    zero_add, Multiset.coe_singleton, Multiset.singleton_add, thread]

/-- **The compiled schemas present the reference semantics exactly**, on tagged rows. -/
theorem eqStep_iff {prog : Program} {W : Multiset Tm} {n : ℕ} (hTag : ∀ r ∈ W, Tagged r)
    (s' : Multiset Tm × ℕ) : EqStep prog (W, n) s' ↔ ORewrites (compiled prog) (W, n) s' := by
  constructor
  · intro step
    cases step with
    | call j t F n θ mgu =>
        refine .fire j ⟨[thread t], [], F, θ, rfl, rfl, ?_, ?_, (compiled_rows _ n θ F).symm⟩
        · simp
        · exact (isMGU_tagged_iff (k := 40)).mpr mgu
  · intro step
    cases step with
    | fire j fires =>
        obtain ⟨taken, read, F, θ, takeLength, readLength, hW, mgu, rfl⟩ := fires
        have readNil : read = [] := List.length_eq_zero_iff.mp (by
          rw [← readLength]; rfl)
        subst readNil
        obtain ⟨r, rfl⟩ : ∃ r, taken = [r] := List.length_eq_one_iff.mp (by
          rw [← takeLength]; rfl)
        have rIn : r ∈ W := by rw [hW]; simp
        obtain ⟨k, s, rfl⟩ := hTag r rIn
        have unifies : θ.applyTerm (tagged 40 ((prog.get j).lhs.at n)) = θ.applyTerm (tagged k s) :=
          mgu.unifies (tagged 40 ((prog.get j).lhs.at n), tagged k s)
            (by simp [problem, compiled, compile, ptag_at])
        rw [apply_tagged, apply_tagged, tagged_inj] at unifies
        obtain ⟨rfl, -⟩ := unifies
        have mgu' : IsMGU [((prog.get j).lhs.at n, s)] θ := by
          have tag : IsMGU [(tagged 40 ((prog.get j).lhs.at n), tagged 40 s)] θ := mgu
          exact isMGU_tagged_iff.mp tag
        subst hW
        have start : (([tagged 40 s] : List Tm) : Multiset Tm) + (((([] : List Tm)) : Multiset Tm) + F) =
            thread s ::ₘ F := by
          simp [thread]
        rw [start, show compiled prog j = compile (prog.get j) from rfl, compiled_rows]
        exact .call j s F n θ mgu'

theorem eqStep_tagged {prog : Program} {s s' : Multiset Tm × ℕ} (step : EqStep prog s s')
    (hTag : ∀ r ∈ s.1, Tagged r) : ∀ r ∈ s'.1, Tagged r := by
  cases step with
  | call j t F n θ mgu =>
      intro r member
      rcases Multiset.mem_cons.mp member with rfl | member
      · exact tagged_tagged 40 _
      · obtain ⟨r₀, r₀In, rfl⟩ := Multiset.mem_map.mp member
        exact (hTag r₀ (Multiset.mem_cons_of_mem r₀In)).apply θ

theorem eqRuns_iff {prog : Program} {s : Multiset Tm × ℕ} (hTag : ∀ r ∈ s.1, Tagged r)
    (s' : Multiset Tm × ℕ) :
    Relation.ReflTransGen (EqStep prog) s s' ↔ Relation.ReflTransGen (ORewrites (compiled prog)) s s' := by
  constructor
  · intro path
    suffices Relation.ReflTransGen (ORewrites (compiled prog)) s s' ∧ ∀ r ∈ s'.1, Tagged r from this.1
    induction path with
    | refl => exact ⟨.refl, hTag⟩
    | @tail b c _ step ih =>
        obtain ⟨run, hTag'⟩ := ih
        obtain ⟨W, n⟩ := b
        exact ⟨run.tail ((eqStep_iff hTag' c).mp step), eqStep_tagged step hTag'⟩
  · intro path
    suffices Relation.ReflTransGen (EqStep prog) s s' ∧ ∀ r ∈ s'.1, Tagged r from this.1
    induction path with
    | refl => exact ⟨.refl, hTag⟩
    | @tail b c _ step ih =>
        obtain ⟨run, hTag'⟩ := ih
        obtain ⟨W, n⟩ := b
        have source := (eqStep_iff hTag' c).mpr step
        exact ⟨run.tail source, eqStep_tagged source hTag'⟩

/-! ## Adequacy -/

/-- **Adequacy of pattern equations.** From tagged rows naming only scope `0`, every reference run
is matched by a run of translated firings of the ordinary step to a configuration representing its
end, and every run of translated firings ends in a configuration representing the end of a
reference run. -/
theorem equations_execution (prog : Program) (l : List Tm) (hTag : ∀ r ∈ l, Tagged r)
    (bounded : ∀ t ∈ l, Bounded 1 t) (W : Multiset Tm) (m : ℕ) :
    (Relation.ReflTransGen (EqStep prog) ((l : Multiset Tm), 1) (W, m) →
      ∃ D, Relation.ReflTransGen (Translated (compiled prog)) (openInitial l, 1) (D, m) ∧
        ORepresents D W m) ∧
    (∀ D, Relation.ReflTransGen (Translated (compiled prog)) (openInitial l, 1) (D, m) →
      ∃ W', Relation.ReflTransGen (EqStep prog) ((l : Multiset Tm), 1) (W', m) ∧
        ORepresents D W' m) := by
  have hTag' : ∀ r ∈ ((l : Multiset Tm), 1).1, Tagged r := fun r member =>
    hTag r (Multiset.mem_coe.mp member)
  obtain ⟨sound, complete⟩ := oexecution (compiled_single prog) l bounded W m
  refine ⟨fun path => sound ((eqRuns_iff hTag' _).mp path), fun D run => ?_⟩
  obtain ⟨W', path, rep⟩ := complete D run
  exact ⟨W', (eqRuns_iff hTag' _).mpr path, rep⟩

/-- **Soundness for one step from any represented configuration.** -/
theorem eqStep_sound {prog : Program} {C : Config} {n : ℕ} {W : Multiset Tm}
    (rep : ORepresents C W n) (hTag : ∀ r ∈ W, Tagged r) {s' : Multiset Tm × ℕ}
    (step : EqStep prog (W, n) s') :
    ∃ D : Config, Translated (compiled prog) (C, n) (D, s'.2) ∧ ORepresents D s'.1 s'.2 := by
  cases (eqStep_iff hTag s').mp step with
  | fire j fires =>
      obtain ⟨taken, read, valid, rep'⟩ := osound rep fires
      exact ⟨_, .fire j taken read valid, rep'⟩

/-- **Completeness for one firing from any represented configuration.** -/
theorem eqFiring_complete {prog : Program} {C : Config} {n : ℕ} {W : Multiset Tm}
    (rep : ORepresents C W n) (hTag : ∀ r ∈ W, Tagged r) {q : Config × ℕ}
    (firing : Translated (compiled prog) (C, n) q) :
    ∃ W', EqStep prog (W, n) (W', q.2) ∧ ORepresents q.1 W' q.2 := by
  cases firing with
  | fire j taken read valid =>
      obtain ⟨W', fires, rep'⟩ := ocomplete (compiled_single prog j) rep valid
      exact ⟨W', (eqStep_iff hTag _).mpr (.fire j fires), rep'⟩

/-! ## The answer multiset is exact -/

/-- **The answers of a call**, in program order: one for each equation whose left-hand side unifies
with the call, renamed apart into scope `n`; each is the right-hand side and the other rows under the
total unifier's most general unifier. -/
def answers (prog : Program) (n : ℕ) (t : Tm) (F : Multiset Tm) : List (Multiset Tm) :=
  prog.filterMap fun e => (unifyTotal [(e.lhs.at n, t)]).map fun θ =>
    thread (θ.applyTerm (e.rhs.at n)) ::ₘ F.map θ.applyTerm

open Classical in
/-- The configurations reached by the admitted firings of each equation's schema on one call
occurrence, in program order. -/
noncomputable def stepAnswers (prog : Program) (n : ℕ) (C : Config) (o : Occ) : List Config :=
  prog.filterMap fun e =>
    if ((compile e).firing n [o] []).Valid A Occ.label C then
      some (((compile e).firing n [o] []).result Occ.label C)
    else none

/-- An admitted firing makes its selected problem solvable. -/
theorem valid_unifiable {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {r : Schema} {taken read : List Occ} (valid : (r.firing n taken read).Valid A Occ.label C) :
    ∃ σ : Subst rows, Unifies σ (schemaProblem r n μ taken read) := by
  obtain ⟨σ, models⟩ := valid.firing.consistent
  have problem : (r.firing n taken read).selection.problem Occ.label (r.firing n taken read).rule C =
      C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl
  rw [problem] at models
  simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true] at models
  obtain ⟨⟨old, takeModels⟩, readModels⟩ := models
  have takeLength : r.take.length = taken.length := by
    have h : (r.take.map (Pat.at n)).length = taken.length := valid.firing.take_length
    rwa [List.length_map] at h
  have readLength : r.read.length = read.length := by
    have h : (r.read.map (Pat.at n)).length = read.length := valid.firing.read_length
    rwa [List.length_map] at h
  exact ⟨σ, (models_new_iff ((solved.solutions σ).mp old) takeLength readLength).mp
    ⟨takeModels, readModels⟩⟩

theorem sdiff_singleton (s : Finset Occ) (o : Occ) : s \ [o].toFinset = s.erase o := by
  ext x
  simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_singleton, Finset.mem_erase]
  tauto

/-- **The firing of an equation on a call occurrence**, for a most general unifier of the call with
the equation's left-hand side: it is admitted, and its result represents the answer. -/
theorem call_firing {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {o : Occ} (present : o ∈ C.present) {t : Tm} (reads : readAt μ o = thread t)
    (e : Equation) {θ : Subst rows} (mgu : IsMGU [(e.lhs.at n, t)] θ) :
    ((compile e).firing n [o] []).Valid A Occ.label C ∧
      ORepresents (((compile e).firing n [o] []).result Occ.label C)
        (thread (θ.applyTerm (e.rhs.at n)) ::ₘ ((C.present.erase o).val.map (readAt μ)).map θ.applyTerm)
        (n + 1) := by
  have mgu' : IsMGU (schemaProblem (compile e) n μ [o] []) θ := by
    show IsMGU [(tagged 40 (e.lhs.at n), readAt μ o)] θ
    rw [reads]
    exact isMGU_tagged_iff.mpr mgu
  obtain ⟨valid, solved', rows⟩ := ofire_at (r := compile e) (taken := [o]) (read := []) solved
    (List.nodup_singleton o)
    (fun x h => by rw [List.mem_singleton.mp h]; exact present)
    (fun x h => absurd h List.not_mem_nil) (fun x _ h => absurd h List.not_mem_nil) rfl rfl mgu'
  refine ⟨valid, θ ∘ₛ μ, solved', ?_⟩
  rw [rows, sdiff_singleton]
  simp only [compile, List.map_cons, List.map_nil, ptag_at, apply_tagged, Multiset.coe_singleton, thread]
  rw [add_comm, Multiset.singleton_add]

/-- **A firing on the call is admitted exactly when the equation's left-hand side unifies with the
call.** -/
theorem call_valid_iff {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {o : Occ} (present : o ∈ C.present) {t : Tm} (reads : readAt μ o = thread t) (e : Equation) :
    ((compile e).firing n [o] []).Valid A Occ.label C ↔ ∃ δ : Subst rows, Unifies δ [(e.lhs.at n, t)] := by
  constructor
  · intro valid
    obtain ⟨σ, unifies⟩ := valid_unifiable solved valid
    have tag : Unifies σ [(tagged 40 (e.lhs.at n), tagged 40 t)] := by
      have same : Unifies σ [(tagged 40 (e.lhs.at n), readAt μ o)] := unifies
      rwa [reads] at same
    exact ⟨σ, (unifies_tagged_iff σ 40 _ _).mp tag⟩
  · intro unifiable
    obtain ⟨θ, mgu⟩ := exists_isMGU unifiable
    exact (call_firing solved present reads e mgu).1

/-- **The answer multiset is exact.** From a configuration with a solved form, at a call occurrence
reading as the thread `t`, the admitted firings of the equations' schemas on that occurrence, in
program order, correspond one to one with the program's answers to `t`, and each result represents
its answer. -/
theorem answers_exact (prog : Program) {C : Config} {n : ℕ} {μ : Subst rows}
    (solved : SolvedForm C n μ) {o : Occ} (present : o ∈ C.present) {t : Tm}
    (reads : readAt μ o = thread t) :
    List.Forall₂ (fun D W => ORepresents D W (n + 1)) (stepAnswers prog n C o)
      (answers prog n t ((C.present.erase o).val.map (readAt μ))) := by
  induction prog with
  | nil => exact .nil
  | cons e prog ih =>
      cases accepted : unifyTotal [(e.lhs.at n, t)] with
      | none =>
          have fails : ¬ ∃ δ : Subst rows, Unifies δ [(e.lhs.at n, t)] :=
            (unifyTotal_none_iff_not_unifiable (σ := rows) _).mp accepted
          have invalid : ¬ ((compile e).firing n [o] []).Valid A Occ.label C := fun valid =>
            fails ((call_valid_iff solved present reads e).mp valid)
          have left : stepAnswers (e :: prog) n C o = stepAnswers prog n C o := by
            unfold stepAnswers
            exact List.filterMap_cons_none (by simp [invalid])
          have right : answers (e :: prog) n t ((C.present.erase o).val.map (readAt μ)) =
              answers prog n t ((C.present.erase o).val.map (readAt μ)) := by
            unfold answers
            exact List.filterMap_cons_none (by simp [accepted])
          rw [left, right]
          exact ih
      | some θ =>
          obtain ⟨valid, rep⟩ := call_firing solved present reads e (isMGU_of_unifyTotal accepted)
          have left : stepAnswers (e :: prog) n C o =
              ((compile e).firing n [o] []).result Occ.label C :: stepAnswers prog n C o := by
            unfold stepAnswers
            exact List.filterMap_cons_some (by simp [valid])
          have right : answers (e :: prog) n t ((C.present.erase o).val.map (readAt μ)) =
              (thread (θ.applyTerm (e.rhs.at n)) ::ₘ
                ((C.present.erase o).val.map (readAt μ)).map θ.applyTerm) ::
                answers prog n t ((C.present.erase o).val.map (readAt μ)) := by
            unfold answers
            exact List.filterMap_cons_some (by simp [accepted])
          rw [left, right]
          exact .cons rep ih

/-- **No equation, no firing**: a represented call that unifies with no left-hand side has no
translated firing at all. It stays as it is, and its configuration is unchanged and consistent. -/
theorem stuck_iff {prog : Program} {C : Config} {n : ℕ} {W : Multiset Tm}
    (rep : ORepresents C W n) (hTag : ∀ r ∈ W, Tagged r) :
    (∀ q, ¬ Translated (compiled prog) (C, n) q) ↔ ∀ s', ¬ EqStep prog (W, n) s' := by
  constructor
  · intro stuck s' step
    obtain ⟨D, firing, -⟩ := eqStep_sound rep hTag step
    exact stuck _ firing
  · intro stuck q firing
    obtain ⟨W', step, -⟩ := eqFiring_complete rep hTag firing
    exact stuck _ step

#print axioms apply_tagged
#print axioms isMGU_tagged_iff
#print axioms eqStep_iff
#print axioms eqStep_tagged
#print axioms eqRuns_iff
#print axioms equations_execution
#print axioms eqStep_sound
#print axioms eqFiring_complete
#print axioms valid_unifiable
#print axioms call_firing
#print axioms call_valid_iff
#print axioms answers_exact
#print axioms stuck_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations
