import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramCompiledObstruction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquationsControls

/-!
# Pattern `let` with capture sets

A let site `k` has a pattern `p`, a body `b`, and a **capture pattern** `c` naming what the body
shares with its context. The thread `letAt k v w` unifies the site's pattern with the value `v` and
its capture pattern with the captured context `w`, two ways, and continues with the body
(`LetStep`). The site's own variables are renamed apart in every activation; the context reaches
the body only through the captures.

* **A let site is a lifted equation** (`letStep_eqStep`): every let step is a step of the lifted
  program, one equation `(= (letAt k p c) b)` per site, with the same result. So let runs are runs
  of the compiled account on the step (`let_execution`). The converse holds only for threads whose
  expression is a let row: a thread whose expression is a bare variable would also narrow against a
  lifted left-hand side.
* **Activations share only captures** (`let_fresh_vars`): every variable of a let activation's result
  occurs in the rows before it or is a fresh variable of the activation's own scope, as in
  `ScopedVariables.different_activations_only_share_captures`.
* **Controls**: `let (pair $a $b) = (pair 1 2) in (pair $b $a)` gives `(pair 2 1)` (`let_swap`);
  a captured caller variable reaches the body and stays correlated with the caller's other rows
  (`capture_shares`); the same body without the capture gets a fresh variable, and the caller's
  row is untouched (`uncaptured_fresh`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramLet

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-- A let site: pattern, capture pattern and body. -/
structure LetSite where
  pat : Pat
  captures : Pat
  body : Pat

/-- The let expression of site `k` on the value `v` with captured context `w`. -/
def letAt (k : ℕ) (v w : Tm) : Tm := tagged 46 (node (.const k) (node v w))

/-- **The reference semantics of let sites**: the site's pattern, renamed apart into the fresh scope
`n`, is unified with the value and its capture pattern with the captured context; the thread
continues with the body under a most general unifier, which binds the caller's variables in every
row. -/
inductive LetStep (sites : List LetSite) : Multiset Tm × ℕ → Multiset Tm × ℕ → Prop
  | bind (k : Fin sites.length) (v w : Tm) (F : Multiset Tm) (n : ℕ) (θ : Subst rows)
      (mgu : IsMGU [((sites.get k).pat.at n, v), ((sites.get k).captures.at n, w)] θ) :
      LetStep sites (thread (letAt k v w) ::ₘ F, n)
        (thread (θ.applyTerm ((sites.get k).body.at n)) ::ₘ F.map θ.applyTerm, n + 1)

/-- **The lifted equation of a let site**: `(= (letAt k p c) b)`. -/
def lifted (k : ℕ) (site : LetSite) : ProgramEquations.Equation :=
  ⟨ptag 46 (.cell (.sym k) (.cell site.pat site.captures)), site.body⟩

/-- The lifted program: one equation per site, in order. -/
def liftedProgram (sites : List LetSite) : Program :=
  sites.zipIdx.map fun site => lifted site.2 site.1

theorem liftedProgram_length (sites : List LetSite) : (liftedProgram sites).length = sites.length := by
  simp [liftedProgram]

theorem liftedProgram_get (sites : List LetSite) (k : Fin sites.length) :
    (liftedProgram sites).get ⟨k, by rw [liftedProgram_length]; exact k.2⟩ = lifted k (sites.get k) := by
  simp [liftedProgram]

/-- The lifted call problem has the let problem's unifiers and variables. -/
theorem isMGU_lifted_iff {k : ℕ} {p c v w : Tm} {θ : Subst rows} :
    IsMGU [(tagged 46 (node (.const k) (node p c)), tagged 46 (node (.const k) (node v w)))] θ ↔
      IsMGU [(p, v), (c, w)] θ := by
  have unifiers : ∀ δ : Subst rows,
      Unifies δ [(tagged 46 (node (.const k) (node p c)), tagged 46 (node (.const k) (node v w)))] ↔
        Unifies δ [(p, v), (c, w)] := by
    intro δ
    rw [unifies_single, apply_tagged, apply_tagged, tagged_inj, apply_node, apply_node, apply_node,
      apply_node, node_inj, node_inj]
    simp [Unifies]
  have fv : ∀ a b : Tm, (tagged 46 (node (.const k) (node a b))).freeVars = a.freeVars ∪ b.freeVars := by
    intro a b
    ext x
    rw [freeVars_tagged, mem_freeVars_node, mem_freeVars_node, Finset.mem_union]
    simp [Term.freeVars]
  have vars : eqVars [(tagged 46 (node (.const k) (node p c)), tagged 46 (node (.const k) (node v w)))] =
      eqVars [(p, v), (c, w)] := by
    simp only [eqVars, fv]
    ext x
    simp only [Finset.mem_union, Finset.notMem_empty, or_false]
    tauto
  exact ⟨fun mgu => mgu.congr unifiers vars, fun mgu => mgu.congr (fun δ => (unifiers δ).symm) vars.symm⟩

/-- **A let site is a lifted equation**: every let step is a step of the lifted program, with the
same result. -/
theorem letStep_eqStep {sites : List LetSite} {s s' : Multiset Tm × ℕ} (step : LetStep sites s s') :
    EqStep (liftedProgram sites) s s' := by
  cases step with
  | bind k v w F n θ mgu =>
      have call := EqStep.call (prog := liftedProgram sites) ⟨k, by rw [liftedProgram_length]; exact k.2⟩
        (letAt k v w) F n θ (by
          rw [liftedProgram_get]
          show IsMGU [(tagged 46 (node (.const k) (node ((sites.get k).pat.at n)
            ((sites.get k).captures.at n))), tagged 46 (node (.const k) (node v w)))] θ
          exact isMGU_lifted_iff.mpr mgu)
      rw [liftedProgram_get] at call
      exact call

theorem letRuns_eqRuns {sites : List LetSite} {s s' : Multiset Tm × ℕ}
    (run : Relation.ReflTransGen (LetStep sites) s s') :
    Relation.ReflTransGen (EqStep (liftedProgram sites)) s s' := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (letStep_eqStep step)

/-- **Let runs on the step**: from tagged rows naming only scope `0`, every run of let steps is
matched by a run of translated firings of the compiled lifted program, ending in a configuration
that represents its end. -/
theorem let_execution (sites : List LetSite) (l : List Tm) (hTag : ∀ r ∈ l, Tagged r)
    (bounded : ∀ t ∈ l, Bounded 1 t) (W : Multiset Tm) (m : ℕ)
    (run : Relation.ReflTransGen (LetStep sites) ((l : Multiset Tm), 1) (W, m)) :
    ∃ D, Relation.ReflTransGen (Translated (compiled (liftedProgram sites))) (openInitial l, 1) (D, m) ∧
      ORepresents D W m :=
  (equations_execution (liftedProgram sites) l hTag bounded W m).1 (letRuns_eqRuns run)

/-- **Activations share only captures**: every variable of a let activation's result occurs in the
rows before it, or is a fresh variable of the activation's scope. -/
theorem let_fresh_vars {sites : List LetSite} {W W' : Multiset Tm} {n n' : ℕ}
    (hTag : ∀ r ∈ W, Tagged r) (step : LetStep sites (W, n) (W', n')) :
    ∀ t ∈ W', ∀ v ∈ t.freeVars, (∃ t₀ ∈ W, v ∈ t₀.freeVars) ∨ v.1 = n := by
  have rewrite := (eqStep_iff hTag (W', n')).mp (letStep_eqStep step)
  cases rewrite with
  | fire j fires =>
      intro t tIn v vIn
      rcases ProgramCompiled.fresh_vars fires t tIn v vIn with old | ⟨scope, -⟩
      · exact .inl old
      · exact .inr scope

/-! ## Controls -/

def kOne : Tm := .const 61
def kTwo : Tm := .const 62
def kUnit : Tm := .const 63

/-- `(pair x y)`. -/
def pair (x y : Tm) : Tm := tagged 64 (node x y)
def ppair (x y : Pat) : Pat := ptag 64 (.cell x y)

theorem ppair_at (x y : Pat) (n : ℕ) : (ppair x y).at n = pair (x.at n) (y.at n) := rfl

theorem apply_pair (σ : Subst rows) (x y : Tm) : σ.applyTerm (pair x y) = pair (σ.applyTerm x) (σ.applyTerm y) := by
  rw [pair, apply_tagged, apply_node]
  rfl

theorem pair_inj {x y x' y' : Tm} : pair x y = pair x' y' ↔ x = x' ∧ y = y' := by
  rw [pair, pair, tagged_inj, node_inj]
  simp

theorem unifies_pair_iff (δ : Subst rows) (x y x' y' : Tm) :
    Unifies δ [(pair x y, pair x' y')] ↔ δ.applyTerm x = δ.applyTerm x' ∧ δ.applyTerm y = δ.applyTerm y' := by
  rw [unifies_single, apply_pair, apply_pair, pair_inj]

/-- `let (pair $a $b) = (pair 1 2) in (pair $b $a)`, capturing nothing. -/
def swapSite : LetSite := ⟨ppair (.var 0) (.var 1), .sym 63, ppair (.var 1) (.var 0)⟩

theorem letAt_inj {k k' : ℕ} {v w v' w' : Tm} (h : letAt k v w = letAt k' v' w') :
    k = k' ∧ v = v' ∧ w = w' := by
  rw [letAt, letAt, tagged_inj, node_inj, node_inj, Term.const.injEq] at h
  exact h.2

/-- A let step from a thread beside rows that are not let threads fires on that thread. -/
theorem letStep_inv {sites : List LetSite} {k₀ : Fin sites.length} {v₀ w₀ : Tm} {G : Multiset Tm}
    {n : ℕ} {s' : Multiset Tm × ℕ} (notLet : ∀ r ∈ G, ∀ (k : ℕ) (v w : Tm), r ≠ thread (letAt k v w))
    (step : LetStep sites (thread (letAt k₀ v₀ w₀) ::ₘ G, n) s') :
    ∃ θ, IsMGU [((sites.get k₀).pat.at n, v₀), ((sites.get k₀).captures.at n, w₀)] θ ∧
      s' = (thread (θ.applyTerm ((sites.get k₀).body.at n)) ::ₘ G.map θ.applyTerm, n + 1) := by
  generalize hs : (thread (letAt k₀ v₀ w₀) ::ₘ G, n) = start at step
  cases step with
  | bind k v w F n' θ mgu =>
      obtain ⟨hW, rfl⟩ := Prod.mk.inj hs
      rcases Multiset.cons_eq_cons.mp hW with ⟨same, rfl⟩ | ⟨-, cs, hG, -⟩
      · obtain ⟨hk, rfl, rfl⟩ := letAt_inj ((tagged_inj.mp same).2)
        have : k₀ = k := Fin.ext hk
        subst this
        exact ⟨θ, mgu, rfl⟩
      · exact absurd rfl (notLet _ (by rw [hG]; exact Multiset.mem_cons_self _ _) k v w)

/-- **Control: the pattern binds both components.** A let step from the thread exists, and every
one answers `(pair 2 1)`. -/
theorem let_swap (n : ℕ) :
    (∃ s', LetStep [swapSite] (thread (letAt 0 (pair kOne kTwo) kUnit) ::ₘ 0, n) s') ∧
      ∀ s', LetStep [swapSite] (thread (letAt 0 (pair kOne kTwo) kUnit) ::ₘ 0, n) s' →
        s' = (thread (pair kTwo kOne) ::ₘ 0, n + 1) := by
  have answer : ∀ θ : Subst rows, Unifies θ [((swapSite.pat).at n, pair kOne kTwo),
      ((swapSite.captures).at n, kUnit)] → θ.applyTerm ((swapSite.body).at n) = pair kTwo kOne := by
    intro θ h
    have first := h _ List.mem_cons_self
    change θ.applyTerm (pair (.var (n, 0)) (.var (n, 1))) = θ.applyTerm (pair kOne kTwo) at first
    rw [apply_pair, apply_pair, pair_inj] at first
    obtain ⟨a, b⟩ := first
    change θ.applyTerm (pair (.var (n, 1)) (.var (n, 0))) = _
    rw [apply_pair]
    change pair (θ (n, 1)) (θ (n, 0)) = _
    change θ (n, 0) = kOne at a
    change θ (n, 1) = kTwo at b
    rw [a, b]
  constructor
  · let δ : Subst rows := fun v => if v = (n, 0) then kOne else if v = (n, 1) then kTwo else .var v
    have unifies : Unifies δ [((swapSite.pat).at n, pair kOne kTwo), ((swapSite.captures).at n, kUnit)] := by
      intro e member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change δ.applyTerm (pair (.var (n, 0)) (.var (n, 1))) = δ.applyTerm (pair kOne kTwo)
        rw [apply_pair, apply_pair]
        change pair (δ (n, 0)) (δ (n, 1)) = pair kOne kTwo
        simp [δ]
      · rfl
    obtain ⟨θ, mgu⟩ := exists_isMGU ⟨δ, unifies⟩
    exact ⟨_, LetStep.bind (sites := [swapSite]) ⟨0, by decide⟩ (pair kOne kTwo) kUnit 0 n θ mgu⟩
  · intro s' step
    obtain ⟨θ, mgu, rfl⟩ := letStep_inv (k₀ := ⟨0, by decide⟩)
      (fun r h => absurd h (Multiset.notMem_zero r)) step
    rw [Multiset.map_zero]
    exact congrArg (fun t => (thread t ::ₘ (0 : Multiset Tm), n + 1)) (answer θ mgu.unifies)

/-- The caller's variable, at scope `0`, and a data row holding it. -/
def vy : Tm := .var (0, 0)
def out (x : Tm) : Tm := tagged 70 x

theorem out_not_let : ∀ r ∈ ({out vy} : Multiset Tm), ∀ (k : ℕ) (v w : Tm), r ≠ thread (letAt k v w) := by
  intro r h k v w same
  rw [Multiset.mem_singleton] at h
  rw [h, out, thread, tagged_inj] at same
  exact absurd same.1 (by decide)

/-- `let $a = 1 in (pair $a $z)`, capturing `$z`. -/
def captureSite : LetSite := ⟨.var 0, .var 1, ppair (.var 0) (.var 1)⟩

/-- **Control: a captured variable is shared.** With the caller's variable `$y` captured as `$z`,
the body's second component and the caller's row `(out $y)` agree after the step. -/
theorem capture_shares (n : ℕ) (pos : 0 < n) :
    (∃ s', LetStep [captureSite] (thread (letAt 0 kOne vy) ::ₘ {out vy}, n) s') ∧
      ∀ s', LetStep [captureSite] (thread (letAt 0 kOne vy) ::ₘ {out vy}, n) s' →
        ∃ u, s' = (thread (pair kOne u) ::ₘ {out u}, n + 1) := by
  constructor
  · let δ : Subst rows := fun v => if v = (n, 0) then kOne else if v = (n, 1) then vy else .var v
    have far : ((0, 0) : ℕ × ℕ) ≠ (n, 0) ∧ ((0, 0) : ℕ × ℕ) ≠ (n, 1) := by
      constructor <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
    have unifies : Unifies δ [((captureSite.pat).at n, kOne), ((captureSite.captures).at n, vy)] := by
      intro e member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change δ (n, 0) = kOne
        simp [δ]
      · change δ (n, 1) = δ (0, 0)
        have ne : ((n, 1) : ℕ × ℕ) ≠ (n, 0) := by simp
        simp only [δ, if_neg far.1, if_neg far.2, if_neg ne, ↓reduceIte]
        rfl
    obtain ⟨θ, mgu⟩ := exists_isMGU ⟨δ, unifies⟩
    exact ⟨_, LetStep.bind (sites := [captureSite]) ⟨0, by decide⟩ kOne vy {out vy} n θ mgu⟩
  · intro s' step
    obtain ⟨θ, mgu, rfl⟩ := letStep_inv (k₀ := ⟨0, by decide⟩) out_not_let step
    have first := mgu.unifies _ List.mem_cons_self
    have second := mgu.unifies _ (List.mem_cons_of_mem _ List.mem_cons_self)
    change θ (n, 0) = kOne at first
    change θ (n, 1) = θ (0, 0) at second
    refine ⟨θ (0, 0), ?_⟩
    show (thread (θ.applyTerm (pair (.var (n, 0)) (.var (n, 1)))) ::ₘ
        ({out vy} : Multiset Tm).map θ.applyTerm, n + 1) =
      (thread (pair kOne (θ (0, 0))) ::ₘ {tagged 70 (θ (0, 0))}, n + 1)
    rw [apply_pair, Multiset.map_singleton, out, vy, apply_tagged, Subst.applyTerm_var,
      Subst.applyTerm_var, Subst.applyTerm_var, first, second]

/-- `let $a = 1 in (pair $a $z)`, capturing nothing: `$z` is the activation's own. -/
def freshSite : LetSite := ⟨.var 0, .sym 63, ppair (.var 0) (.var 1)⟩

/-- **Control: an uncaptured variable is fresh.** Without the capture, the body's second component
is a fresh variable of the activation's scope, never the caller's `$y`, and the caller's row is
untouched. -/
theorem uncaptured_fresh (n : ℕ) (pos : 0 < n) :
    (∃ s', LetStep [freshSite] (thread (letAt 0 kOne kUnit) ::ₘ {out vy}, n) s') ∧
      (∀ s', LetStep [freshSite] (thread (letAt 0 kOne kUnit) ::ₘ {out vy}, n) s' →
        s' = (thread (pair kOne (.var (n, 1))) ::ₘ {out vy}, n + 1)) ∧
      (Term.var (n, 1) : Tm) ≠ vy := by
  have vars : ∀ v : ℕ × ℕ, v ≠ (n, 0) →
      v ∉ eqVars [((freshSite.pat).at n, kOne), ((freshSite.captures).at n, kUnit)] := by
    intro v ne member
    change v ∈ eqVars [((Term.var (n, 0) : Tm), kOne), ((Term.const 63 : Tm), kUnit)] at member
    simp [eqVars, Term.freeVars, kOne, kUnit] at member
    exact ne member
  refine ⟨?_, ?_, ?_⟩
  · let δ : Subst rows := fun v => if v = (n, 0) then kOne else .var v
    have unifies : Unifies δ [((freshSite.pat).at n, kOne), ((freshSite.captures).at n, kUnit)] := by
      intro e member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change δ (n, 0) = kOne
        simp [δ]
      · rfl
    obtain ⟨θ, mgu⟩ := exists_isMGU ⟨δ, unifies⟩
    exact ⟨_, LetStep.bind (sites := [freshSite]) ⟨0, by decide⟩ kOne kUnit {out vy} n θ mgu⟩
  · intro s' step
    obtain ⟨θ, mgu, rfl⟩ := letStep_inv (k₀ := ⟨0, by decide⟩) out_not_let step
    have first := mgu.unifies _ List.mem_cons_self
    change θ (n, 0) = kOne at first
    have fresh : θ (n, 1) = .var (n, 1) := mgu.relevant.fixes _ (vars _ (by
      simp only [ne_eq, Prod.mk.injEq, true_and]; omega))
    have caller : θ (0, 0) = .var (0, 0) := mgu.relevant.fixes _ (vars _ (by
      simp only [ne_eq, Prod.mk.injEq, not_and]; intro h; omega))
    show (thread (θ.applyTerm (pair (.var (n, 0)) (.var (n, 1)))) ::ₘ
        ({out vy} : Multiset Tm).map θ.applyTerm, n + 1) =
      (thread (pair kOne (.var (n, 1))) ::ₘ {tagged 70 (.var (0, 0))}, n + 1)
    rw [apply_pair, Multiset.map_singleton, out, vy, apply_tagged, Subst.applyTerm_var,
      Subst.applyTerm_var, Subst.applyTerm_var, first, fresh, caller]
  · intro h
    rw [vy, Term.var.injEq, Prod.mk.injEq] at h
    omega

#print axioms isMGU_lifted_iff
#print axioms letStep_eqStep
#print axioms letRuns_eqRuns
#print axioms let_execution
#print axioms let_fresh_vars
#print axioms letStep_inv
#print axioms let_swap
#print axioms capture_shares
#print axioms uncaptured_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramLet
