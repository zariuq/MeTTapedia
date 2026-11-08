import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramLet

/-!
# The converse of the lifted `let`, on configurations of let shape

`ProgramLet.letStep_eqStep` shows every let step is a step of the lifted program, one equation
`(= (letAt k p c) b)` per site. The converse fails for a thread whose expression is a bare
variable, which the lifted left-hand side narrows. On configurations of **let shape** it holds.

* `LetShapedExpr`: a thread expression is tagged, and when its tag is the let tag it is a let row
  `letAt k v w`. `LetShaped`: every thread's expression is of let shape.
* **One step** (`eqStep_letStep`): from tagged rows of let shape, every step of the lifted program
  is a let step, with the same result.
* **Shape is kept** (`letStep_shaped`) when every site's body is of let shape (`BodyShaped`), so
  **runs** of the lifted program from such rows are let runs (`eqRuns_letRuns`), and on the step
  the compiled lifted program and the let sites have the same runs, both ways
  (`let_execution_iff`).
* **Controls**: from the let thread of the swap site, every lifted step is a let step
  (`swap_converse`); a bare-variable thread has a lifted step (it is narrowed into a let row) and no
  let step (`bare_variable_narrows`), so the shape hypothesis is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramLet

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-- A thread expression of let shape: tagged, and a let row when its tag is the let tag. -/
def LetShapedExpr (s : Tm) : Prop :=
  ∃ k s', s = tagged k s' ∧ (k = 46 → ∃ j v w, s' = node (.const j) (node v w))

/-- Rows of let shape: every thread's expression is of let shape. -/
def LetShaped (W : Multiset Tm) : Prop := ∀ r ∈ W, ∀ s, r = thread s → LetShapedExpr s

theorem LetShapedExpr.apply {s : Tm} (shaped : LetShapedExpr s) (θ : Subst rows) :
    LetShapedExpr (θ.applyTerm s) := by
  obtain ⟨k, s', rfl, letRow⟩ := shaped
  refine ⟨k, θ.applyTerm s', apply_tagged θ k s', fun h => ?_⟩
  obtain ⟨j, v, w, rfl⟩ := letRow h
  exact ⟨j, θ.applyTerm v, θ.applyTerm w, by rw [apply_node, apply_node]; rfl⟩

/-- **The converse, one step**: from tagged rows of let shape, every step of the lifted program is a
let step with the same result. -/
theorem eqStep_letStep {sites : List LetSite} {W : Multiset Tm} {n : ℕ} {s' : Multiset Tm × ℕ}
    (shaped : LetShaped W) (step : EqStep (liftedProgram sites) (W, n) s') :
    LetStep sites (W, n) s' := by
  generalize hs : (W, n) = start at step
  cases step with
  | call j t F n' θ mgu =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      obtain ⟨jv, jlt⟩ := j
      obtain ⟨k, s₀, rfl, letRow⟩ := shaped _ (Multiset.mem_cons_self _ _) _ rfl
      have site : (liftedProgram sites).get ⟨jv, jlt⟩ = lifted jv (sites.get ⟨jv, by
          rw [← liftedProgram_length]; exact jlt⟩) :=
        liftedProgram_get sites ⟨jv, by rw [← liftedProgram_length]; exact jlt⟩
      rw [site] at mgu ⊢
      have unifies := mgu.unifies _ List.mem_cons_self
      change θ.applyTerm (tagged 46 (node (.const jv) (node ((sites.get ⟨jv, _⟩).pat.at n)
        ((sites.get ⟨jv, _⟩).captures.at n)))) = θ.applyTerm (tagged k s₀) at unifies
      rw [apply_tagged, apply_tagged, tagged_inj] at unifies
      obtain ⟨rfl, body⟩ := unifies
      obtain ⟨j, v, w, rfl⟩ := letRow rfl
      simp only [apply_node, node_inj] at body
      have hj : jv = j := by
        have h := body.1
        rw [Subst.applyTerm_const, Subst.applyTerm_const] at h
        cases h
        rfl
      subst hj
      have mgu' : IsMGU [((sites.get ⟨jv, _⟩).pat.at n, v), ((sites.get ⟨jv, _⟩).captures.at n, w)] θ :=
        isMGU_lifted_iff.mp mgu
      exact LetStep.bind ⟨jv, _⟩ v w F n θ mgu'

/-- A site whose body has let shape. -/
def BodyShaped (site : LetSite) : Prop :=
  ∃ k p, site.body = ptag k p ∧ (k = 46 → ∃ j a b, p = .cell (.sym j) (.cell a b))

theorem body_shaped_at {site : LetSite} (shaped : BodyShaped site) (n : ℕ) :
    LetShapedExpr (site.body.at n) := by
  obtain ⟨k, p, hb, letRow⟩ := shaped
  rw [hb, ptag_at]
  refine ⟨k, p.at n, rfl, fun h => ?_⟩
  obtain ⟨j, a, b, rfl⟩ := letRow h
  exact ⟨j, a.at n, b.at n, rfl⟩

/-- **Let shape is kept** when every site's body has let shape, on tagged rows. -/
theorem letStep_shaped {sites : List LetSite} (bodies : ∀ site ∈ sites, BodyShaped site)
    {s s' : Multiset Tm × ℕ} (step : LetStep sites s s') (shaped : LetShaped s.1)
    (hTag : ∀ r ∈ s.1, Tagged r) : LetShaped s'.1 := by
  cases step with
  | bind k v w F n θ mgu =>
      intro r member s₁ hr
      rcases Multiset.mem_cons.mp member with rfl | member
      · obtain ⟨-, rfl⟩ := tagged_inj.mp hr
        exact (body_shaped_at (bodies _ (List.get_mem _ k)) n).apply θ
      · obtain ⟨r₀, r₀In, rfl⟩ := Multiset.mem_map.mp member
        obtain ⟨k₀, s₀, rfl⟩ := hTag r₀ (Multiset.mem_cons_of_mem r₀In)
        rw [apply_tagged] at hr
        obtain ⟨rfl, rfl⟩ := tagged_inj.mp hr
        exact (shaped _ (Multiset.mem_cons_of_mem r₀In) s₀ rfl).apply θ

/-- **Runs of the lifted program from rows of let shape are let runs.** -/
theorem eqRuns_letRuns {sites : List LetSite} (bodies : ∀ site ∈ sites, BodyShaped site)
    {s s' : Multiset Tm × ℕ} (run : Relation.ReflTransGen (EqStep (liftedProgram sites)) s s')
    (shaped : LetShaped s.1) (hTag : ∀ r ∈ s.1, Tagged r) : Relation.ReflTransGen (LetStep sites) s s' := by
  suffices Relation.ReflTransGen (LetStep sites) s s' ∧ LetShaped s'.1 ∧ ∀ r ∈ s'.1, Tagged r from this.1
  induction run with
  | refl => exact ⟨.refl, shaped, hTag⟩
  | @tail b c _ step ih =>
      obtain ⟨path, shaped', hTag'⟩ := ih
      obtain ⟨W, m⟩ := b
      have letStep := eqStep_letStep shaped' step
      exact ⟨path.tail letStep, letStep_shaped bodies letStep shaped' hTag', eqStep_tagged step hTag'⟩

/-- **On the step, the compiled lifted program and the let sites have the same runs**, from tagged
rows of let shape naming only scope `0`, when every site's body has let shape. -/
theorem let_execution_iff (sites : List LetSite) (bodies : ∀ site ∈ sites, BodyShaped site)
    (l : List Tm) (hTag : ∀ r ∈ l, Tagged r) (shaped : LetShaped (l : Multiset Tm))
    (bounded : ∀ t ∈ l, Bounded 1 t) (W : Multiset Tm) (m : ℕ) :
    (Relation.ReflTransGen (LetStep sites) ((l : Multiset Tm), 1) (W, m) →
      ∃ D, Relation.ReflTransGen (Translated (compiled (liftedProgram sites))) (openInitial l, 1) (D, m) ∧
        ORepresents D W m) ∧
    (∀ D, Relation.ReflTransGen (Translated (compiled (liftedProgram sites))) (openInitial l, 1) (D, m) →
      ∃ W', Relation.ReflTransGen (LetStep sites) ((l : Multiset Tm), 1) (W', m) ∧ ORepresents D W' m) := by
  refine ⟨let_execution sites l hTag bounded W m, fun D run => ?_⟩
  obtain ⟨W', path, rep⟩ := (equations_execution (liftedProgram sites) l hTag bounded W m).2 D run
  exact ⟨W', eqRuns_letRuns bodies path shaped fun r member => hTag r (Multiset.mem_coe.mp member), rep⟩

/-! ## Controls -/

theorem swap_body_shaped : ∀ site ∈ [swapSite], BodyShaped site := by
  intro site member
  rw [List.mem_singleton] at member
  subst member
  exact ⟨64, .cell (.var 1) (.var 0), rfl, fun h => absurd h (by decide)⟩

/-- **From the swap site's let thread, every lifted step is a let step.** -/
theorem swap_converse (n : ℕ) (s' : Multiset Tm × ℕ)
    (step : EqStep (liftedProgram [swapSite]) (thread (letAt 0 (pair kOne kTwo) kUnit) ::ₘ 0, n) s') :
    LetStep [swapSite] (thread (letAt 0 (pair kOne kTwo) kUnit) ::ₘ 0, n) s' := by
  refine eqStep_letStep (fun r member s hr => ?_) step
  rw [Multiset.mem_cons] at member
  rcases member with rfl | member
  · obtain ⟨-, rfl⟩ := tagged_inj.mp hr
    exact ⟨46, _, rfl, fun _ => ⟨0, _, _, rfl⟩⟩
  · exact absurd member (Multiset.notMem_zero _)

/-- The caller's variable `$z`. -/
def vz : Tm := .var (0, 0)

/-- **The shape hypothesis is necessary**: a bare-variable thread has a lifted step, narrowing it into
a let row, and no let step. -/
theorem bare_variable_narrows (n : ℕ) (pos : 0 < n) :
    (∃ s', EqStep (liftedProgram [swapSite]) (thread vz ::ₘ 0, n) s') ∧
      ∀ s', ¬ LetStep [swapSite] (thread vz ::ₘ 0, n) s' := by
  refine ⟨?_, fun s' step => ?_⟩
  · obtain ⟨θ, mgu⟩ := exists_isMGU (P := [(((liftedProgram [swapSite]).get ⟨0, by decide⟩).lhs.at n, vz)])
      ⟨Subst.single (σ := rows) (0, 0) (((liftedProgram [swapSite]).get ⟨0, by decide⟩).lhs.at n),
        fun e member => by
          rw [List.mem_singleton] at member
          subst member
          show _ = (Subst.single (σ := rows) (0, 0) _) (0, 0)
          rw [Subst.single_eq (σ := rows)]
          refine Subst.applyTerm_eq_self fun v hv => Subst.single_ne (σ := rows) _ fun h => ?_
          have := at_scope n _ v hv
          rw [h] at this
          omega⟩
    exact ⟨_, EqStep.call ⟨0, by decide⟩ vz 0 n θ mgu⟩
  · generalize hs : (thread vz ::ₘ (0 : Multiset Tm), n) = start at step
    cases step with
    | bind k v w F n' θ mgu =>
        obtain ⟨hW, -⟩ := Prod.mk.inj hs
        have : thread (letAt k v w) ∈ thread vz ::ₘ (0 : Multiset Tm) := by
          rw [hW]
          exact Multiset.mem_cons_self _ _
        rw [Multiset.mem_cons] at this
        rcases this with h | h
        · have := (tagged_inj.mp h).2
          cases this
        · exact absurd h (Multiset.notMem_zero _)

#print axioms LetShapedExpr.apply
#print axioms eqStep_letStep
#print axioms body_shaped_at
#print axioms letStep_shaped
#print axioms eqRuns_letRuns
#print axioms let_execution_iff
#print axioms swap_converse
#print axioms bare_variable_narrows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramLet
