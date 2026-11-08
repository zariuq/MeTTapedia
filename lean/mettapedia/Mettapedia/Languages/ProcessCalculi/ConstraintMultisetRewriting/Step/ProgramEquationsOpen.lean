import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramTranslation

/-!
# Schemas over open rows: unification in both directions, and its firings on the step

Rows may contain logic variables. A schema fires on open rows by **two-way unification**: its take
and read patterns, renamed apart into the fresh scope `n`, are unified with selected rows, and a most
general unifier `θ` is applied to every row, so a binding made for one row is seen by every row that
shares the variable (`OFires`). This is the substitution semantics of narrowing over a multiset.

On the step, the same schema fires as in `ProgramTranslation` (`Schema.firing`): no unifier is
computed; the take and read equations join the equation store. The two are related through a
**solved form** (`SolvedForm`): an idempotent substitution `μ` whose instances are exactly the
solutions of the configuration's knowledge. A configuration represents the rows its occurrences read
through `μ` (`ORepresents`).

* `models_step_iff`: after a firing, the solutions of the new knowledge are exactly the instances of
  `θ ∘ μ`, for every most general unifier `θ` of the selected problem (Lassez–Maher–Marriott's
  correspondence between equation stores and their unifiers).
* `osound`, `ocomplete`: every open rewrite from represented rows is matched by one admitted firing
  of the same schema, and every admitted firing is the image of an open rewrite; the result
  represents the rewritten rows.
* `opath_sound`, `opath_complete`, `oexecution`: the same for runs from the initial configuration.
  Solved forms are not unique (a variable-to-variable binding may go either way), so represented
  rows agree at every solution of the knowledge (`represents_agree`), not syntactically.

A most general unifier is the semantic notion (`IsMGU`); the total unifier `unifyTotal` provides
one whenever a unifier exists (`isMGU_of_unifyTotal`, `exists_isMGU`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquationsOpen

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation

/-! ## Most general unifiers -/

/-- The unification problem of patterns, copied at scope `n`, against rows. -/
def problem (n : ℕ) (ps : List Pat) (ts : List Tm) : List (Tm × Tm) :=
  List.zipWith (fun p t => (p.at n, t)) ps ts

/-- **A most general unifier** of `P`: it unifies `P`, every unifier of `P` is an instance of it,
and it is idempotent and relevant to the variables of `P`. -/
structure IsMGU (P : List (Tm × Tm)) (θ : Subst rows) : Prop where
  unifies : Unifies θ P
  general : ∀ δ : Subst rows, Unifies δ P → θ.moreGeneral δ
  relevant : θ.RelevantIdempotent (eqVars P)

theorem isMGU_of_unifyTotal {P : List (Tm × Tm)} {θ : Subst rows}
    (accepted : unifyTotal P = some θ) : IsMGU P θ :=
  ⟨unifyTotal_sound P θ accepted, fun δ unifies => unifyTotal_mgu P θ accepted δ unifies,
    unifyTotal_relevantIdempotent P θ accepted⟩

theorem exists_isMGU {P : List (Tm × Tm)} (unifiable : ∃ δ : Subst rows, Unifies δ P) :
    ∃ θ, IsMGU P θ := by
  obtain ⟨θ, accepted⟩ := unifyTotal_complete unifiable
  exact ⟨θ, isMGU_of_unifyTotal accepted⟩

/-- Problems with the same unifiers and the same variables have the same most general unifiers. -/
theorem IsMGU.congr {P Q : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ)
    (same : ∀ δ : Subst rows, Unifies δ P ↔ Unifies δ Q) (vars : eqVars P = eqVars Q) :
    IsMGU Q θ :=
  ⟨(same θ).mp mgu.unifies, fun δ unifies => mgu.general δ ((same δ).mpr unifies),
    vars ▸ mgu.relevant⟩

theorem unifies_append (δ : Subst rows) (P Q : List (Tm × Tm)) :
    Unifies δ (P ++ Q) ↔ Unifies δ P ∧ Unifies δ Q := by
  simp only [Unifies, List.mem_append]
  constructor
  · intro all
    exact ⟨fun e member => all e (.inl member), fun e member => all e (.inr member)⟩
  · rintro ⟨one, two⟩ e (member | member)
    · exact one e member
    · exact two e member

theorem unifies_problem_iff (δ : Subst rows) (n : ℕ) {ps : List Pat} {ts : List Tm}
    (lengths : ps.length = ts.length) :
    Unifies δ (problem n ps ts) ↔
      List.Forall₂ (fun p t => δ.applyTerm (p.at n) = δ.applyTerm t) ps ts := by
  induction ps generalizing ts with
  | nil =>
      cases ts with
      | nil => simp [problem, Unifies]
      | cons _ _ => simp at lengths
  | cons p ps ih =>
      cases ts with
      | nil => simp at lengths
      | cons t ts =>
          have rest := ih (ts := ts) (by simpa using lengths)
          simp only [problem, Unifies, List.zipWith_cons_cons, List.forall_mem_cons,
            List.forall₂_cons] at rest ⊢
          exact and_congr Iff.rfl rest

theorem mem_problem {n : ℕ} : ∀ {ps : List Pat} {ts : List Tm} {e : Tm × Tm},
    e ∈ problem n ps ts → ∃ p ∈ ps, ∃ t ∈ ts, e = (p.at n, t)
  | [], _, _, h => by simp [problem] at h
  | _ :: _, [], _, h => by simp [problem] at h
  | p :: ps, t :: ts, e, h => by
      simp only [problem, List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨p, List.mem_cons_self, t, List.mem_cons_self, rfl⟩
      · obtain ⟨p', member, t', member', rfl⟩ := mem_problem (ps := ps) (ts := ts) h
        exact ⟨p', List.mem_cons_of_mem _ member, t', List.mem_cons_of_mem _ member', rfl⟩

/-! ## Open rows and their rewrites -/

/-- An occurrence read through a substitution. -/
def readAt (μ : Subst rows) (o : Occ) : Tm := μ.applyTerm o.label

/-- **A schema rewrites open rows at scope `n`**: rows `taken` and `read` from `W`, and a most general
unifier `θ` of the schema's take and read patterns, renamed apart into scope `n`, against them. The
taken rows are replaced by the made terms; `θ` is applied to every row. -/
def OFires (r : Schema) (n : ℕ) (W W' : Multiset Tm) : Prop :=
  ∃ (taken read : List Tm) (F : Multiset Tm) (θ : Subst rows),
    r.take.length = taken.length ∧ r.read.length = read.length ∧
    W = (taken : Multiset Tm) + ((read : Multiset Tm) + F) ∧
    IsMGU (problem n r.take taken ++ problem n r.read read) θ ∧
    W' = ((r.make.map fun q => θ.applyTerm (q.at n) : List Tm) : Multiset Tm) +
      (((read.map θ.applyTerm : List Tm) : Multiset Tm) + F.map θ.applyTerm)

/-- **Open rewrites of a program**: one of its schemas fires at the current scope, and the next
rewrite uses the next scope. -/
inductive ORewrites {ι : Type*} (schema : ι → Schema) : Multiset Tm × ℕ → Multiset Tm × ℕ → Prop
  | fire {W W' : Multiset Tm} {n : ℕ} (i : ι) (fires : OFires (schema i) n W W') :
      ORewrites schema (W, n) (W', n + 1)

/-! ## Solved forms -/

/-- **A solved form of a configuration below scope `n`**: occurrences were made below `n` and name
only scopes below `n`; the solutions of the knowledge are exactly the substitutions absorbing `μ`;
`μ` is idempotent, fixes every variable from scope `n` on, and maps every earlier variable to a
term below `n`. -/
structure SolvedForm (C : Config) (n : ℕ) (μ : Subst rows) : Prop where
  occurrences : ∀ o ∈ C.present, o.scope < n ∧ Bounded n o.label
  solutions : ∀ σ : Subst rows, A.Models σ C.equations ↔ σ.Absorbs μ
  idempotent : μ.Absorbs μ
  fixes : ∀ v : ℕ × ℕ, n ≤ v.1 → μ v = .var v
  bounded : ∀ v : ℕ × ℕ, v.1 < n → Bounded n (μ v)

/-- **A configuration represents open rows** below scope `n`: it has a solved form through which
its occurrences read as `W`. -/
def ORepresents (C : Config) (W : Multiset Tm) (n : ℕ) : Prop :=
  ∃ μ : Subst rows, SolvedForm C n μ ∧ C.present.val.map (readAt μ) = W

namespace SolvedForm

variable {C : Config} {n : ℕ} {μ : Subst rows}

theorem consistent (solved : SolvedForm C n μ) : A.Consistent C.equations :=
  ⟨μ, (solved.solutions μ).mpr solved.idempotent⟩

theorem read_bounded (solved : SolvedForm C n μ) {t : Tm} (bounded : Bounded n t) :
    Bounded n (μ.applyTerm t) := fun x member => by
  obtain ⟨v, vIn, occurs⟩ := (Subst.mem_freeVars_applyTerm (σ := rows)).mp member
  exact solved.bounded v (bounded v vIn) x occurs

theorem fixes_at (solved : SolvedForm C n μ) (p : Pat) : μ.applyTerm (p.at n) = p.at n :=
  Subst.applyTerm_eq_self fun v member => solved.fixes v (le_of_eq (at_scope n p v member).symm)

end SolvedForm

/-- The problem of a schema instance at scope `n` against occurrences read through `μ`. -/
def schemaProblem (r : Schema) (n : ℕ) (μ : Subst rows) (taken read : List Occ) :
    List (Tm × Tm) :=
  problem n r.take (taken.map (readAt μ)) ++ problem n r.read (read.map (readAt μ))

theorem schemaProblem_vars {r : Schema} {n : ℕ} {μ : Subst rows} {taken read : List Occ}
    {x : ℕ × ℕ} (member : x ∈ eqVars (schemaProblem r n μ taken read)) :
    x.1 = n ∨ ∃ o ∈ taken ++ read, x ∈ (readAt μ o).freeVars := by
  obtain ⟨e, eIn, occurs⟩ := (mem_eqVars (σ := rows)).mp member
  have fromProblem : ∀ {ps : List Pat} {os : List Occ}, e ∈ problem n ps (os.map (readAt μ)) →
      (∀ o ∈ os, o ∈ taken ++ read) →
        x.1 = n ∨ ∃ o ∈ taken ++ read, x ∈ (readAt μ o).freeVars := by
    intro ps os eIn' inside
    obtain ⟨p, -, t, tIn, rfl⟩ := mem_problem eIn'
    obtain ⟨o, oIn, rfl⟩ := List.mem_map.mp tIn
    rcases occurs with occurs | occurs
    · exact .inl (at_scope n p x occurs)
    · exact .inr ⟨o, inside o oIn, occurs⟩
  rcases List.mem_append.mp eIn with eIn | eIn
  · exact fromProblem eIn fun o h => List.mem_append_left _ h
  · exact fromProblem eIn fun o h => List.mem_append_right _ h

/-- **Every variable of the selected problem is fixed by the solved form** and belongs to a scope up
to `n`. -/
theorem SolvedForm.problem_vars {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {r : Schema} {taken read : List Occ} (inside : ∀ o ∈ taken ++ read, o ∈ C.present)
    {x : ℕ × ℕ} (member : x ∈ eqVars (schemaProblem r n μ taken read)) :
    μ x = .var x ∧ x.1 < n + 1 := by
  rcases schemaProblem_vars member with scope | ⟨o, oIn, occurs⟩
  · exact ⟨solved.fixes x (le_of_eq scope.symm), by omega⟩
  · exact ⟨solved.idempotent.var_fixed o.label x occurs,
      Nat.lt_succ_of_lt (solved.read_bounded (solved.occurrences o (inside o oIn)).2 x occurs)⟩

/-! ## The knowledge after a firing -/

/-- For a substitution absorbing the solved form, the firing's new equations are the selected
problem. -/
theorem models_new_iff {μ σ : Subst rows} (absorbs : σ.Absorbs μ) {n : ℕ} {r : Schema}
    {taken read : List Occ} (takeLength : r.take.length = taken.length)
    (readLength : r.read.length = read.length) :
    (A.Models σ (Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken) ∧
        A.Models σ (Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read)) ↔
      Unifies σ (schemaProblem r n μ taken read) := by
  have takeLength' : (r.take.map (Pat.at n)).length = taken.length := by
    rw [List.length_map]; exact takeLength
  have readLength' : (r.read.map (Pat.at n)).length = read.length := by
    rw [List.length_map]; exact readLength
  have takeRows : r.take.length = (taken.map (readAt μ)).length := by
    rw [List.length_map]; exact takeLength
  have readRows : r.read.length = (read.map (readAt μ)).length := by
    rw [List.length_map]; exact readLength
  rw [models_take_iff σ n takeLength', models_take_iff σ n readLength', schemaProblem,
    unifies_append, unifies_problem_iff σ n takeRows, unifies_problem_iff σ n readRows,
    List.forall₂_map_right_iff, List.forall₂_map_right_iff]
  have same : ∀ o : Occ, σ.applyTerm (readAt μ o) = σ.applyTerm o.label := fun o =>
    absorbs.applyTerm o.label
  simp only [same]

/-- **The solutions after a firing are the instances of `θ ∘ μ`**, for every most general unifier `θ`
of the selected problem. -/
theorem models_step_iff {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {r : Schema} {taken read : List Occ}
    (takeLength : r.take.length = taken.length) (readLength : r.read.length = read.length)
    (inside : ∀ o ∈ taken ++ read, o ∈ C.present)
    {θ : Subst rows} (mgu : IsMGU (schemaProblem r n μ taken read) θ) (σ : Subst rows) :
    A.Models σ (C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ []) ↔
      σ.Absorbs (θ ∘ₛ μ) := by
  simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
  constructor
  · rintro ⟨⟨old, takeModels⟩, readModels⟩
    have absorbs : σ.Absorbs μ := (solved.solutions σ).mp old
    have unifies := (models_new_iff absorbs takeLength readLength).mp ⟨takeModels, readModels⟩
    have absorbsθ : σ.Absorbs θ :=
      Subst.absorbs_of_moreGeneral mgu.relevant.absorbs (mgu.general σ unifies)
    exact absorbsθ.comp absorbs
  · intro absorbs
    have absorbsμ : σ.Absorbs μ := fun v => by
      have once := absorbs.applyTerm (μ v)
      rw [Subst.applyTerm_comp, show μ.applyTerm (μ v) = μ v from solved.idempotent v] at once
      rw [← once]
      exact absorbs v
    have absorbsθ : σ.Absorbs θ := fun v => by
      by_cases fixed : μ v = .var v
      · have once := absorbs v
        rwa [Subst.comp_apply, fixed, Subst.applyTerm_var] at once
      · have notIn : v ∉ eqVars (schemaProblem r n μ taken read) := fun member =>
          fixed (solved.problem_vars inside member).1
        rw [mgu.relevant.fixes v notIn, Subst.applyTerm_var]
    have unifies : Unifies σ (schemaProblem r n μ taken read) := fun e member => by
      rw [← absorbsθ.applyTerm e.1, ← absorbsθ.applyTerm e.2, mgu.unifies e member]
    obtain ⟨takeModels, readModels⟩ := (models_new_iff absorbsμ takeLength readLength).mpr unifies
    exact ⟨⟨(solved.solutions σ).mpr absorbsμ, takeModels⟩, readModels⟩

/-! ## The firing of a schema instance on open rows -/

/-- **The core of both directions**: for a most general unifier `θ` of the selected problem, the
schema's firing at a fresh scope is admitted, `θ ∘ μ` is a solved form of its result, and the result
reads as the made terms under `θ` beside the remaining rows under `θ`. -/
theorem ofire_at {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ) {r : Schema}
    {taken read : List Occ} (takenNodup : taken.Nodup) (takenIn : ∀ o ∈ taken, o ∈ C.present)
    (readIn : ∀ o ∈ read, o ∈ C.present) (apart : ∀ o ∈ taken, o ∉ read)
    (takeLength : r.take.length = taken.length) (readLength : r.read.length = read.length)
    {θ : Subst rows} (mgu : IsMGU (schemaProblem r n μ taken read) θ) :
    (r.firing n taken read).Valid A Occ.label C ∧
      SolvedForm ((r.firing n taken read).result Occ.label C) (n + 1) (θ ∘ₛ μ) ∧
      ((r.firing n taken read).result Occ.label C).present.val.map (readAt (θ ∘ₛ μ)) =
        ((C.present \ taken.toFinset).val.map (readAt μ)).map θ.applyTerm +
          ((r.make.map fun q => θ.applyTerm (q.at n) : List Tm) : Multiset Tm) := by
  have inside : ∀ o ∈ taken ++ read, o ∈ C.present := fun o h =>
    (List.mem_append.mp h).elim (takenIn o) (readIn o)
  have solutions := models_step_iff solved takeLength readLength inside mgu
  have problem : (r.firing n taken read).selection.problem Occ.label (r.firing n taken read).rule C =
      C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl
  have idempotent : (θ ∘ₛ μ).Absorbs (θ ∘ₛ μ) :=
    Subst.comp_idempotent mgu.relevant.absorbs fun v => by
      refine Subst.applyTerm_eq_self fun x member => ?_
      rcases Finset.mem_union.mp (mgu.relevant.freeVars_applyTerm_subset (μ v) member) with old | new
      · exact solved.idempotent.var_fixed (.var v) x old
      · exact (solved.problem_vars inside new).1
  have models : A.Models (θ ∘ₛ μ) ((r.firing n taken read).selection.problem Occ.label
      (r.firing n taken read).rule C) := by
    rw [problem]
    exact (solutions _).mpr idempotent
  have disjointMade : ∀ o ∈ madeAt n 0 r.make, o ∉ C.present := fun o made present => by
    have scope := (madeAt_mem made).1
    have lt := (solved.occurrences o present).1
    omega
  have takeLength' : (r.take.map (Pat.at n)).length = taken.length := by
    rw [List.length_map]; exact takeLength
  have readLength' : (r.read.map (Pat.at n)).length = read.length := by
    rw [List.length_map]; exact readLength
  have valid : (r.firing n taken read).Valid A Occ.label C := by
    refine ⟨⟨takenNodup, madeAt_nodup n 0 r.make, takeLength', readLength', madeAt_label n 0 r.make,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨θ ∘ₛ μ, models⟩, ?_⟩, ?_⟩
    · intro o h
      exact takenIn o (List.mem_toFinset.mp h)
    · intro o h
      exact readIn o (List.mem_toFinset.mp h)
    · exact Finset.disjoint_left.mpr fun o h₁ h₂ =>
        apart o (List.mem_toFinset.mp h₁) (List.mem_toFinset.mp h₂)
    · exact Finset.disjoint_left.mpr fun o h₁ h₂ => disjointMade o (List.mem_toFinset.mp h₁) h₂
    · intro q h
      simp [Selection.commit] at h
    · intro check h
      simp [Schema.firing, Schema.rule] at h
    · intro query h
      simp [Schema.firing] at h
  have resultEqs : ((r.firing n taken read).result Occ.label C).equations =
      C.equations ++ Selection.equations (T := Tm) Occ.label (r.take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label (r.read.map (Pat.at n)) read ++ [] := rfl
  have resultPresent : ((r.firing n taken read).result Occ.label C).present =
      (C.present \ taken.toFinset) ∪ (madeAt n 0 r.make).toFinset := rfl
  have madeRead : ∀ (i : ℕ) (qs : List Pat),
      (madeAt n i qs).map (readAt (θ ∘ₛ μ)) = qs.map fun q => θ.applyTerm (q.at n) := by
    intro i qs
    induction qs generalizing i with
    | nil => rfl
    | cons q qs ih =>
        simp only [madeAt, List.map_cons, ih]
        congr 1
        simp only [readAt, Subst.applyTerm_comp, solved.fixes_at]
  refine ⟨valid, ⟨?_, ?_, idempotent, ?_, ?_⟩, ?_⟩
  · intro o member
    rw [resultPresent, Finset.mem_union, Finset.mem_sdiff] at member
    rcases member with ⟨old, -⟩ | made
    · exact ⟨Nat.lt_succ_of_lt (solved.occurrences o old).1,
        (solved.occurrences o old).2.mono (Nat.le_succ n)⟩
    · obtain ⟨scope, -, q, -, label⟩ := madeAt_mem (List.mem_toFinset.mp made)
      rw [scope, label]
      exact ⟨Nat.lt_succ_self n, at_bounded n q⟩
  · intro σ
    rw [resultEqs]
    exact solutions σ
  · intro v le
    change θ.applyTerm (μ v) = .var v
    rw [solved.fixes v (by omega), Subst.applyTerm_var]
    exact mgu.relevant.fixes v fun member => by
      have := (solved.problem_vars inside member).2
      omega
  · intro v lt x member
    change x ∈ (θ.applyTerm (μ v)).freeVars at member
    rcases Finset.mem_union.mp (mgu.relevant.freeVars_applyTerm_subset (μ v) member) with old | new
    · by_cases below : v.1 < n
      · exact Nat.lt_succ_of_lt (solved.bounded v below x old)
      · rw [solved.fixes v (by omega), Term.mem_freeVars_var (σ := rows)] at old
        rw [old]
        exact lt
    · exact (solved.problem_vars inside new).2
  · have disjoint : Disjoint (C.present \ taken.toFinset) (madeAt n 0 r.make).toFinset :=
      Finset.disjoint_left.mpr fun o h₁ h₂ =>
        disjointMade o (List.mem_toFinset.mp h₂) (Finset.mem_sdiff.mp h₁).1
    rw [resultPresent, ← Finset.disjUnion_eq_union _ _ disjoint]
    change Multiset.map (readAt (θ ∘ₛ μ))
      ((C.present \ taken.toFinset).val + (madeAt n 0 r.make).toFinset.val) = _
    rw [Multiset.map_add, List.toFinset_val, (madeAt_nodup n 0 r.make).dedup, Multiset.map_coe,
      madeRead 0 r.make, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun o _ => ?_
    simp only [Function.comp_apply, readAt, Subst.applyTerm_comp]

/-! ## Selection bookkeeping -/

theorem pickRows (value : Occ → Tm) : ∀ (L : List Tm) (s : Finset Occ) (F : Multiset Tm),
    s.val.map value = (L : Multiset Tm) + F →
      ∃ os : List Occ, os.Nodup ∧ (∀ o ∈ os, o ∈ s) ∧ os.map value = L ∧
        (s \ os.toFinset).val.map value = F
  | [], s, F, h => ⟨[], List.nodup_nil, fun _ h => absurd h List.not_mem_nil, rfl, by simpa using h⟩
  | a :: L, s, F, h => by
      have mem : a ∈ s.val.map value := by rw [h]; simp
      obtain ⟨o, oIn, rfl⟩ := Multiset.mem_map.mp mem
      have split : (s.erase o).val.map value = (L : Multiset Tm) + F := by
        have hs : s.val = o ::ₘ (s.erase o).val := by rw [Finset.erase_val, Multiset.cons_erase oIn]
        rw [hs, Multiset.map_cons, ← Multiset.cons_coe, Multiset.cons_add] at h
        exact (Multiset.cons_inj_right _).mp h
      obtain ⟨os, nodup, inside, values, rest⟩ := pickRows value L (s.erase o) F split
      refine ⟨o :: os, List.nodup_cons.mpr ⟨fun h => Finset.notMem_erase o s (inside o h), nodup⟩, ?_,
        by simp [values], ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact oIn
        · exact Finset.mem_of_mem_erase (inside x hx)
      · rw [List.toFinset_cons, Finset.sdiff_insert, ← Finset.erase_sdiff_comm]
        exact rest

theorem splitRows (value : Occ → Tm) : ∀ (os : List Occ) (s : Finset Occ), os.Nodup →
    (∀ o ∈ os, o ∈ s) →
      s.val.map value = ((os.map value : List Tm) : Multiset Tm) + (s \ os.toFinset).val.map value
  | [], s, _, _ => by simp
  | o :: os, s, nodup, inside => by
      obtain ⟨notIn, nodup'⟩ := List.nodup_cons.mp nodup
      have oIn : o ∈ s := inside o List.mem_cons_self
      have inside' : ∀ x ∈ os, x ∈ s.erase o := fun x hx =>
        Finset.mem_erase.mpr ⟨fun same => notIn (same ▸ hx), inside x (List.mem_cons_of_mem _ hx)⟩
      have hs : s.val = o ::ₘ (s.erase o).val := by rw [Finset.erase_val, Multiset.cons_erase oIn]
      rw [hs, Multiset.map_cons, splitRows value os (s.erase o) nodup' inside', List.map_cons,
        ← Multiset.cons_coe, Multiset.cons_add, List.toFinset_cons, Finset.sdiff_insert,
        ← Finset.erase_sdiff_comm]

/-! ## Adequacy -/

/-- **Soundness**: every open rewrite from represented rows is matched by one admitted firing of
the same schema at the next scope, whose result represents the rewritten rows. -/
theorem osound {C : Config} {W W' : Multiset Tm} {n : ℕ} {r : Schema}
    (rep : ORepresents C W n) (fires : OFires r n W W') :
    ∃ taken read : List Occ, (r.firing n taken read).Valid A Occ.label C ∧
      ORepresents ((r.firing n taken read).result Occ.label C) W' (n + 1) := by
  obtain ⟨μ, solved, image⟩ := rep
  obtain ⟨takenRows, readRows, F, θ, takeLength, readLength, rfl, mgu, rfl⟩ := fires
  obtain ⟨taken, takenNodup, takenIn, takenValues, rest⟩ :=
    pickRows (readAt μ) takenRows C.present _ image
  obtain ⟨read, -, readIn, readValues, -⟩ :=
    pickRows (readAt μ) readRows (C.present \ taken.toFinset) F rest
  have readPresent : ∀ o ∈ read, o ∈ C.present := fun o h => (Finset.mem_sdiff.mp (readIn o h)).1
  have apart : ∀ o ∈ taken, o ∉ read := fun o h h' =>
    (Finset.mem_sdiff.mp (readIn o h')).2 (List.mem_toFinset.mpr h)
  have takeLength' : r.take.length = taken.length := by
    rw [takeLength, ← takenValues, List.length_map]
  have readLength' : r.read.length = read.length := by
    rw [readLength, ← readValues, List.length_map]
  have mgu' : IsMGU (schemaProblem r n μ taken read) θ := by
    rw [schemaProblem, takenValues, readValues]
    exact mgu
  obtain ⟨valid, solved', rows⟩ :=
    ofire_at solved takenNodup takenIn readPresent apart takeLength' readLength' mgu'
  refine ⟨taken, read, valid, θ ∘ₛ μ, solved', ?_⟩
  rw [rows, rest, Multiset.map_add, Multiset.map_coe]
  exact add_comm _ _

theorem nodup_of_length_le_one {α : Type*} : ∀ {l : List α}, l.length ≤ 1 → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | _ :: _ :: _, h => by simp at h

/-- **Completeness**: every admitted firing of a schema instance at the next scope from represented
rows is the image of an open rewrite of the same schema, and its result represents the rewritten
rows. -/
theorem ocomplete {C : Config} {W : Multiset Tm} {n : ℕ} {r : Schema} (single : r.read.length ≤ 1)
    (rep : ORepresents C W n) {taken read : List Occ}
    (valid : (r.firing n taken read).Valid A Occ.label C) :
    ∃ W', OFires r n W W' ∧ ORepresents ((r.firing n taken read).result Occ.label C) W' (n + 1) := by
  obtain ⟨μ, solved, rfl⟩ := rep
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
  have takenIn : ∀ o ∈ taken, o ∈ C.present := fun o h =>
    valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr h)
  have readIn : ∀ o ∈ read, o ∈ C.present := fun o h =>
    valid.firing.occurrences.kept_subset (List.mem_toFinset.mpr h)
  have apart : ∀ o ∈ taken, o ∉ read := fun o h h' =>
    Finset.disjoint_left.mp valid.firing.occurrences.apart (List.mem_toFinset.mpr h)
      (List.mem_toFinset.mpr h')
  have absorbs : σ.Absorbs μ := (solved.solutions σ).mp old
  have unifies := (models_new_iff absorbs takeLength readLength).mp ⟨takeModels, readModels⟩
  obtain ⟨θ, mgu⟩ := exists_isMGU ⟨σ, unifies⟩
  have takenNodup : taken.Nodup := valid.firing.take_distinct
  obtain ⟨-, solved', rows⟩ :=
    ofire_at solved takenNodup takenIn readIn apart takeLength readLength mgu
  have readNodup : read.Nodup := nodup_of_length_le_one (by rw [← readLength]; exact single)
  have readRest : ∀ o ∈ read, o ∈ C.present \ taken.toFinset := fun o h =>
    Finset.mem_sdiff.mpr ⟨readIn o h, fun h' => apart o (List.mem_toFinset.mp h') h⟩
  have restSplit := splitRows (readAt μ) read (C.present \ taken.toFinset) readNodup readRest
  refine ⟨_, ⟨taken.map (readAt μ), read.map (readAt μ),
    ((C.present \ taken.toFinset) \ read.toFinset).val.map (readAt μ), θ,
    by rw [List.length_map]; exact takeLength, by rw [List.length_map]; exact readLength, ?_, mgu, rfl⟩,
    θ ∘ₛ μ, solved', ?_⟩
  · rw [splitRows (readAt μ) taken C.present takenNodup takenIn, restSplit]
  · rw [rows, restSplit, Multiset.map_add, Multiset.map_coe]
    exact add_comm _ _

/-! ## Runs -/

theorem opath_sound {ι : Type*} {schema : ι → Schema} {p q : Multiset Tm × ℕ}
    (path : Relation.ReflTransGen (ORewrites schema) p q) {C : Config}
    (rep : ORepresents C p.1 p.2) :
    ∃ D : Config, Relation.ReflTransGen (Translated schema) (C, p.2) (D, q.2) ∧
      ORepresents D q.1 q.2 := by
  induction path with
  | refl => exact ⟨C, .refl, rep⟩
  | tail _ step ih =>
      obtain ⟨D, run, rep'⟩ := ih
      cases step with
      | fire i fires =>
          obtain ⟨taken, read, valid, rep''⟩ := osound rep' fires
          exact ⟨_, run.tail (.fire i taken read valid), rep''⟩

theorem opath_complete {ι : Type*} {schema : ι → Schema} (single : ∀ i, (schema i).read.length ≤ 1)
    {p q : Config × ℕ} (path : Relation.ReflTransGen (Translated schema) p q) {W : Multiset Tm}
    (rep : ORepresents p.1 W p.2) :
    ∃ W', Relation.ReflTransGen (ORewrites schema) (W, p.2) (W', q.2) ∧ ORepresents q.1 W' q.2 := by
  induction path with
  | refl => exact ⟨W, .refl, rep⟩
  | tail _ step ih =>
      obtain ⟨W', reductions, rep'⟩ := ih
      cases step with
      | fire i taken read valid =>
          obtain ⟨W'', fires, rep''⟩ := ocomplete (single i) rep' valid
          exact ⟨W'', reductions.tail (.fire i fires), rep''⟩

/-- The initial occurrences of a list of open rows, at scope `0`. -/
def openRows : ℕ → List Tm → List Occ
  | _, [] => []
  | i, t :: l => ⟨t, 0, i⟩ :: openRows (i + 1) l

theorem openRows_mem : ∀ {i : ℕ} {l : List Tm} {o : Occ}, o ∈ openRows i l →
    o.scope = 0 ∧ i ≤ o.index ∧ o.label ∈ l
  | _, [], _, h => absurd h List.not_mem_nil
  | i, t :: l, o, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨rfl, le_rfl, List.mem_cons_self⟩
      · obtain ⟨scope, index, member⟩ := openRows_mem h
        exact ⟨scope, Nat.le_of_succ_le index, List.mem_cons_of_mem _ member⟩

theorem openRows_nodup : ∀ (i : ℕ) (l : List Tm), (openRows i l).Nodup
  | _, [] => List.nodup_nil
  | i, _ :: l => List.nodup_cons.mpr ⟨fun h => Nat.not_succ_le_self i (openRows_mem h).2.1,
      openRows_nodup (i + 1) l⟩

/-- The initial configuration of a list of open rows: no equations, one occurrence per row. -/
noncomputable def openInitial (l : List Tm) : Config := ⟨[], (openRows 0 l).toFinset⟩

/-- The initial occurrences read through the identity are the rows. -/
theorem openRows_read (l : List Tm) : ∀ i, (openRows i l).map (readAt (Subst.id rows)) = l := by
  induction l with
  | nil => intro i; rfl
  | cons t l ih =>
      intro i
      simp only [openRows, List.map_cons, ih]
      simp [readAt, Subst.applyTerm_id]

/-- **The identity is a solved form of the initial configuration**, when its rows name only scope
`0`. -/
theorem openInitial_solved (l : List Tm) (bounded : ∀ t ∈ l, Bounded 1 t) :
    SolvedForm (openInitial l) 1 (Subst.id rows) := by
  refine ⟨?_, fun σ => ⟨fun _ v => rfl, fun _ => SubstitutionAction.models_nil A σ⟩,
    fun v => rfl, fun v _ => rfl, ?_⟩
  · intro o member
    obtain ⟨scope, -, label⟩ := openRows_mem (List.mem_toFinset.mp member)
    rw [scope]
    exact ⟨Nat.zero_lt_one, bounded _ label⟩
  · intro v lt x member
    rw [show Subst.id rows v = .var v from rfl, Term.mem_freeVars_var (σ := rows)] at member
    rw [member]
    exact lt

/-- **The initial configuration represents its rows**, when they name only scope `0`. -/
theorem openInitial_represents (l : List Tm) (bounded : ∀ t ∈ l, Bounded 1 t) :
    ORepresents (openInitial l) (l : Multiset Tm) 1 := by
  refine ⟨Subst.id rows, openInitial_solved l bounded, ?_⟩
  change Multiset.map _ (openRows 0 l).toFinset.val = _
  rw [List.toFinset_val, (openRows_nodup 0 l).dedup, Multiset.map_coe, openRows_read l 0]

/-- **Represented rows agree at every solution of the knowledge.** -/
theorem represents_agree {D : Config} {W W' : Multiset Tm} {m : ℕ}
    (one : ORepresents D W m) (two : ORepresents D W' m) (σ : Subst rows)
    (models : A.Models σ D.equations) : W.map σ.applyTerm = W'.map σ.applyTerm := by
  obtain ⟨μ, solved, rfl⟩ := one
  obtain ⟨μ', solved', rfl⟩ := two
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun o _ => ?_
  simp only [Function.comp_apply, readAt]
  rw [((solved.solutions σ).mp models).applyTerm, ((solved'.solutions σ).mp models).applyTerm]

/-- **Adequacy for runs over open rows.** From the initial configuration of rows naming only scope
`0`, every run of open rewrites is matched by a run of translated firings of the ordinary step to a
configuration representing its end, and every run of translated firings ends in a configuration
representing the end of a run of open rewrites. -/
theorem oexecution {ι : Type*} {schema : ι → Schema} (single : ∀ i, (schema i).read.length ≤ 1)
    (l : List Tm) (bounded : ∀ t ∈ l, Bounded 1 t) (W : Multiset Tm) (m : ℕ) :
    (Relation.ReflTransGen (ORewrites schema) ((l : Multiset Tm), 1) (W, m) →
      ∃ D, Relation.ReflTransGen (Translated schema) (openInitial l, 1) (D, m) ∧ ORepresents D W m) ∧
    (∀ D, Relation.ReflTransGen (Translated schema) (openInitial l, 1) (D, m) →
      ∃ W', Relation.ReflTransGen (ORewrites schema) ((l : Multiset Tm), 1) (W', m) ∧
        ORepresents D W' m) := by
  refine ⟨fun path => opath_sound path (openInitial_represents l bounded), fun D run => ?_⟩
  exact opath_complete single run (openInitial_represents l bounded)

#print axioms isMGU_of_unifyTotal
#print axioms exists_isMGU
#print axioms unifies_problem_iff
#print axioms models_new_iff
#print axioms models_step_iff
#print axioms ofire_at
#print axioms osound
#print axioms ocomplete
#print axioms opath_sound
#print axioms opath_complete
#print axioms openInitial_solved
#print axioms openInitial_represents
#print axioms represents_agree
#print axioms oexecution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquationsOpen
