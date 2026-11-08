import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquations

/-!
# Why a call is one firing only in the compiled form

The compiled account answers a call by one firing of its equation's schema
(`ProgramEquations.answers_exact`). An interpreter is a fixed family of schemas reading equations as
data. This file proves the obstruction that separates the two.

* **A firing introduces only its own pattern variables** (`fresh_vars`): every variable of a row made
  or rewritten by an open firing of a schema at scope `n` already occurs in the rows before, or is
  `(n, x)` for a pattern variable `x` of the schema. So a firing introduces at most as many fresh
  variables as its schema has pattern variables (`fresh_card_le`).
* **The compiled answer of a wide equation has as many fresh variables as its right-hand side**
  (`wide_answer`): the equation `(= (f a) (s $0 … $(k-1)))` answers `(f a)` with `k` distinct
  variables, none in the rows before.
* **No fixed family answers every call in one firing** (`no_fixed_one_firing_interpreter`): for any
  family of schemas whose schemas have at most `V` pattern variables, no single open rewrite of the
  family, from rows below scope `n`, makes a row with `V + 1` variables outside those rows. The wide
  equation with `k = V + 1` needs exactly that. So an interpreter over equations as data answers such
  calls only through administrative firings that allocate the fresh variables, and renaming apart is
  then a run, not a firing; one firing per call needs schemas computed per equation.
* **The call occurrence is consumed** (`call_consumed`): an admitted firing on a call takes its
  occurrence, so no second firing uses it; this is the invocation-control law of the contextual
  native lowering (`ContextualNativeBodies.Body.completed_control_absent`) in the first-order,
  guard-free case.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-- The pattern variables of a schema. -/
def schemaVars (r : Schema) : List ℕ := (r.take ++ r.read ++ r.make).flatMap Pat.vars

theorem freeVars_at {n : ℕ} : ∀ (p : Pat), ∀ v ∈ (p.at n).freeVars, v.1 = n ∧ v.2 ∈ p.vars
  | .var x => fun v hv => by
      rw [Pat.at, Term.mem_freeVars_var (σ := rows)] at hv
      subst hv
      exact ⟨rfl, by simp [Pat.vars]⟩
  | .sym _ => fun v hv => by simp [Pat.at, Term.freeVars] at hv
  | .cell a b => fun v hv => by
      rcases mem_freeVars_node.mp hv with hv | hv
      · obtain ⟨scope, name⟩ := freeVars_at a v hv
        exact ⟨scope, by simp [Pat.vars, name]⟩
      · obtain ⟨scope, name⟩ := freeVars_at b v hv
        exact ⟨scope, by simp [Pat.vars, name]⟩

theorem mem_schemaVars {r : Schema} {p : Pat} (member : p ∈ r.take ++ r.read ++ r.make) {x : ℕ}
    (occurs : x ∈ p.vars) : x ∈ schemaVars r :=
  List.mem_flatMap.mpr ⟨p, member, occurs⟩

/-- **A firing introduces only its own pattern variables.** -/
theorem fresh_vars {r : Schema} {n : ℕ} {W W' : Multiset Tm} (fires : OFires r n W W') :
    ∀ t ∈ W', ∀ v ∈ t.freeVars, (∃ t₀ ∈ W, v ∈ t₀.freeVars) ∨ (v.1 = n ∧ v.2 ∈ schemaVars r) := by
  obtain ⟨taken, read, F, θ, takeLength, readLength, rfl, mgu, rfl⟩ := fires
  -- every variable of the problem occurs in the rows or is a pattern variable at scope `n`
  have problemVars : ∀ v ∈ eqVars (problem n r.take taken ++ problem n r.read read),
      (∃ t₀ ∈ (taken : Multiset Tm) + ((read : Multiset Tm) + F), v ∈ t₀.freeVars) ∨
        (v.1 = n ∧ v.2 ∈ schemaVars r) := by
    intro v member
    obtain ⟨e, eIn, occurs⟩ := (mem_eqVars (σ := rows)).mp member
    have fromProblem : ∀ {ps : List Pat} {ts : List Tm}, e ∈ problem n ps ts →
        (∀ p ∈ ps, p ∈ r.take ++ r.read ++ r.make) → (∀ t ∈ ts, t ∈ (taken : Multiset Tm) +
          ((read : Multiset Tm) + F)) →
        (∃ t₀ ∈ (taken : Multiset Tm) + ((read : Multiset Tm) + F), v ∈ t₀.freeVars) ∨
          (v.1 = n ∧ v.2 ∈ schemaVars r) := by
      intro ps ts eIn' patterns rows
      obtain ⟨p, pIn, t, tIn, rfl⟩ := mem_problem eIn'
      rcases occurs with occurs | occurs
      · obtain ⟨scope, name⟩ := freeVars_at p v occurs
        exact .inr ⟨scope, mem_schemaVars (patterns p pIn) name⟩
      · exact .inl ⟨t, rows t tIn, occurs⟩
    rcases List.mem_append.mp eIn with eIn | eIn
    · exact fromProblem eIn (fun p h => by simp [h]) (fun t h => by simp [h])
    · exact fromProblem eIn (fun p h => by simp [h]) (fun t h => by simp [h])
  -- a variable of `θ s`
  have through : ∀ s : Tm, ∀ v ∈ (θ.applyTerm s).freeVars,
      (∃ w ∈ s.freeVars, v = w) ∨ v ∈ eqVars (problem n r.take taken ++ problem n r.read read) := by
    intro s v member
    obtain ⟨w, wIn, occurs⟩ := (Subst.mem_freeVars_applyTerm (σ := rows)).mp member
    rcases Classical.em (w ∈ eqVars (problem n r.take taken ++ problem n r.read read)) with bound | bound
    · exact .inr (mgu.relevant.range w bound occurs)
    · rw [mgu.relevant.fixes w bound, Term.mem_freeVars_var (σ := rows)] at occurs
      exact .inl ⟨w, wIn, occurs⟩
  intro t tIn v vIn
  rcases Multiset.mem_add.mp tIn with made | rest
  · obtain ⟨q, qIn, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
    rcases through _ v vIn with ⟨w, wIn, rfl⟩ | bound
    · obtain ⟨scope, name⟩ := freeVars_at q v wIn
      exact .inr ⟨scope, mem_schemaVars (by simp [qIn]) name⟩
    · exact problemVars v bound
  · have old : ∃ t₀ ∈ (read : Multiset Tm) + F, t = θ.applyTerm t₀ := by
      rcases Multiset.mem_add.mp rest with readIn | restIn
      · obtain ⟨t₀, t₀In, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp readIn)
        exact ⟨t₀, by simp [t₀In], rfl⟩
      · obtain ⟨t₀, t₀In, rfl⟩ := Multiset.mem_map.mp restIn
        exact ⟨t₀, by simp [t₀In], rfl⟩
    obtain ⟨t₀, t₀In, rfl⟩ := old
    rcases through _ v vIn with ⟨w, wIn, rfl⟩ | bound
    · exact .inl ⟨t₀, by simp [t₀In], wIn⟩
    · exact problemVars v bound

/-- **A firing introduces at most as many fresh variables as its schema has pattern variables.** -/
theorem fresh_card_le {r : Schema} {n : ℕ} {W W' : Multiset Tm} (fires : OFires r n W W')
    {t : Tm} (made : t ∈ W') (X : Finset (ℕ × ℕ)) (inside : X ⊆ t.freeVars)
    (fresh : ∀ v ∈ X, ∀ t₀ ∈ W, v ∉ t₀.freeVars) : X.card ≤ (schemaVars r).toFinset.card := by
  have atScope : ∀ v ∈ X, v.1 = n ∧ v.2 ∈ schemaVars r := fun v member => by
    rcases fresh_vars fires t made v (inside member) with ⟨t₀, t₀In, occurs⟩ | atScope
    · exact absurd occurs (fresh v member t₀ t₀In)
    · exact atScope
  refine Finset.card_le_card_of_injOn Prod.snd (fun v member => ?_) ?_
  · exact List.mem_toFinset.mpr (atScope v member).2
  · intro v vIn w wIn same
    exact Prod.ext ((atScope v vIn).1.trans (atScope w wIn).1.symm) same

/-! ## A wide equation -/

/-- `s $0 … $(k-1)`: a right-hand side with `k` variables. -/
def spine : ℕ → Pat
  | 0 => .sym 99
  | k + 1 => .cell (.var k) (spine k)

theorem freeVars_spine (n : ℕ) : ∀ k : ℕ, ∀ v : ℕ × ℕ, v ∈ ((spine k).at n).freeVars ↔ v.1 = n ∧ v.2 < k
  | 0, v => by simp [spine, Pat.at, Term.freeVars]
  | k + 1, v => by
      rw [spine, Pat.at, mem_freeVars_node, freeVars_spine n k v, Pat.at, Term.mem_freeVars_var (σ := rows)]
      constructor
      · rintro (rfl | ⟨scope, lt⟩)
        · exact ⟨rfl, Nat.lt_succ_self k⟩
        · exact ⟨scope, Nat.lt_succ_of_lt lt⟩
      · rintro ⟨scope, lt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
        · exact .inr ⟨scope, lt⟩
        · exact .inl (Prod.ext scope rfl)

/-- `(= (f a) (s $0 … $(k-1)))`. -/
def wideEquation (k : ℕ) : ProgramEquations.Equation := ⟨ptag 50 (.sym 60), spine k⟩

/-- The variables of the wide answer at scope `n`. -/
def wideVars (n k : ℕ) : Finset (ℕ × ℕ) := (Finset.range k).image fun x => (n, x)

theorem wideVars_card (n k : ℕ) : (wideVars n k).card = k := by
  rw [wideVars, Finset.card_image_of_injective _ (fun x y same => (Prod.mk.inj same).2), Finset.card_range]

/-- **The compiled answer of the wide equation has `k` fresh variables**: for every most general
unifier of the call `(f a)` with the left-hand side at scope `n`, the answer is the right-hand side
itself, whose variables are exactly `(n, 0), …, (n, k-1)`. -/
theorem wide_answer (k n : ℕ) {θ : Subst rows}
    (mgu : IsMGU [((wideEquation k).lhs.at n, tagged 50 (.const 60))] θ) :
    θ.applyTerm ((wideEquation k).rhs.at n) = (spine k).at n ∧
      wideVars n k ⊆ (thread ((spine k).at n)).freeVars := by
  have noVars : eqVars [((wideEquation k).lhs.at n, tagged 50 (.const 60))] = ∅ := by
    show eqVars [(tagged 50 (.const 60), tagged 50 (.const 60))] = ∅
    simp [eqVars, freeVars_tagged, Term.freeVars]
  refine ⟨Subst.applyTerm_eq_self fun v _ => mgu.relevant.fixes v (by simp [noVars]), ?_⟩
  intro v member
  rw [thread, freeVars_tagged, freeVars_spine]
  obtain ⟨x, xIn, rfl⟩ := Finset.mem_image.mp member
  exact ⟨rfl, Finset.mem_range.mp xIn⟩

/-- **No fixed family answers every call in one firing.** For a family of schemas each with at most
`V` pattern variables, no single open rewrite of the family from rows below scope `n` makes a row
with `V + 1` variables outside those rows; the compiled answer of the wide equation with `V + 1`
variables is such a row. -/
theorem no_fixed_one_firing_interpreter {ι : Type*} (family : ι → Schema) (V : ℕ)
    (bound : ∀ i, (schemaVars (family i)).toFinset.card ≤ V) {W W' : Multiset Tm} {n n' : ℕ}
    (below : ∀ t ∈ W, Bounded n t) (step : ORewrites family (W, n) (W', n')) :
    ¬ thread ((spine (V + 1)).at n) ∈ W' := by
  intro member
  cases step with
  | fire i fires =>
      have fresh : ∀ v ∈ wideVars n (V + 1), ∀ t₀ ∈ W, v ∉ t₀.freeVars := by
        intro v vIn t₀ t₀In occurs
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp vIn
        exact absurd (below t₀ t₀In _ occurs) (Nat.lt_irrefl n)
      have inside : wideVars n (V + 1) ⊆ (thread ((spine (V + 1)).at n)).freeVars := by
        intro v vIn
        rw [thread, freeVars_tagged, freeVars_spine]
        obtain ⟨x, xIn, rfl⟩ := Finset.mem_image.mp vIn
        exact ⟨rfl, Finset.mem_range.mp xIn⟩
      have := fresh_card_le fires member _ inside fresh
      rw [wideVars_card] at this
      exact absurd (this.trans (bound i)) (Nat.not_succ_le_self V)

/-- **The call occurrence is consumed**: an admitted firing of an equation's schema on a call takes
its occurrence, so no second firing uses it. -/
theorem call_consumed {C : Config} {n : ℕ} (e : ProgramEquations.Equation) {o : Occ}
    (valid : ((compile e).firing n [o] []).Valid A Occ.label C) :
    o ∉ (((compile e).firing n [o] []).result Occ.label C).present :=
  Selection.Valid.consumed_removed valid.firing (List.mem_singleton_self o)

#print axioms freeVars_at
#print axioms fresh_vars
#print axioms fresh_card_le
#print axioms freeVars_spine
#print axioms wideVars_card
#print axioms wide_answer
#print axioms no_fixed_one_firing_interpreter
#print axioms call_consumed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled
