import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CompletionControls

/-!
# Control: `f(f(x)) ≈ x` restricted to ground instances completes

Over the signature of the superposition controls (one unary function `p`, constants `⊤ < a < b`),
the start is the infinite set of ground instances `p(p(t)) ≈ t`, one for every ground term `t`.

* **A fair infinite run** (`involution_derivation`): stage `i` orients the instance at the `i`-th
  ground term of an enumeration (`enum`, onto by `enum_surjective`), or idles if it is already
  oriented.
* **Its persistent items are the rules `p(p(t)) → t`** (`limit_involution`), and **every critical
  pair is trivial** (`involution_fair`): a left side `p(p(t₁))` inside `p(p(t₂))` sits at `pᵏ(□)`
  with `t₂ = pᵏ(t₁)`. So the run is fair and no equation is left.
* **The rules are convergent and decide the theory** (`involution_convergent`).
* **A word problem** (`p5_p1`, `p1_not_a`): `p⁵(a) ≈ p(a)` follows; `p(a) ≈ a` does not, since
  `p(a)` and `a` are distinct normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion.Involution

open Mettapedia.Logic.LP
open Superposition (Ctx Rw Joins)
open Superposition.Controls (sig a p lt_p ctxP key lt_iff_key)
open Completion.Controls (fill_app fillP irreducible_of_below)
open _root_.Relation (ReflTransGen EqvGen)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Terms of the signature -/

theorem p_injective : Function.Injective p := by
  intro s t same
  have args := eq_of_heq (GroundTerm.app.inj same).2
  exact congrFun args 0

/-- The depth of a context: every context is `pᵏ(□)`. -/
def depth : Ctx sig → ℕ
  | .hole => 0
  | .app _ _ _ inner => depth inner + 1

theorem ctx_fill : ∀ (d : Ctx sig) (t : GroundTerm sig), d.fill t = p^[depth d] t
  | .hole, _ => rfl
  | .app () args i inner, t => by
      rw [Subsingleton.elim i 0, fill_app, ctx_fill inner t, depth, Function.iterate_succ_apply']

/-- Every ground term is `pⁿ(c)` for a constant `c`. -/
theorem term_cases : ∀ t : GroundTerm sig, ∃ (n : ℕ) (c : Fin 3), t = p^[n] (GroundTerm.const c)
  | .const c => ⟨0, c, rfl⟩
  | .app () args => by
      obtain ⟨n, c, same⟩ := term_cases (args 0)
      refine ⟨n + 1, c, ?_⟩
      rw [Function.iterate_succ_apply', ← same]
      show GroundTerm.app () args = GroundTerm.app () fun _ => args 0
      congr 1
      funext i
      rw [Subsingleton.elim i 0]

/-- An enumeration of the ground terms. -/
def enum (i : ℕ) : GroundTerm sig := p^[i / 3] (GroundTerm.const ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩)

theorem enum_surjective (t : GroundTerm sig) : ∃ i, enum i = t := by
  obtain ⟨n, c, rfl⟩ := term_cases t
  refine ⟨3 * n + c.val, ?_⟩
  have div : (3 * n + c.val) / 3 = n := by omega
  have mod : (3 * n + c.val) % 3 = c.val := by omega
  unfold enum
  rw [div]
  congr 2
  exact Fin.ext mod

theorem a_lt_p (t : GroundTerm sig) : a < p t := by
  rw [lt_iff_key]
  show toLex (0, (1 : Fin 3)) < toLex ((ofLex (key t)).1 + 1, (ofLex (key t)).2)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.succ_pos _))

theorem pa_lt_pp (t : GroundTerm sig) : p a < p (p t) := by
  have step := fill_lt_fill ctxP (a_lt_p t)
  rwa [fillP, fillP] at step

/-! ## The run -/

/-- The terms whose instance is oriented before stage `i`. -/
def oriented (i : ℕ) : Set (GroundTerm sig) := {t | ∃ j < i, enum j = t}

/-- **Stage `i`**: the oriented instances as rules, the others as equations. -/
def stage (i : ℕ) : Set (Item sig) :=
  {x | ∃ t, (t ∈ oriented i ∧ x = .rule (p (p t)) t) ∨ (t ∉ oriented i ∧ x = .eqn s(p (p t), t))}

/-- The start: every ground instance `p(p(t)) ≈ t`. -/
def E₀ : Set (Item sig) := {x | ∃ t, x = .eqn s(p (p t), t)}

/-- The completed system: every rule `p(p(t)) → t`. -/
def Rinv : Set (Item sig) := {x | ∃ t, x = .rule (p (p t)) t}

theorem stage_zero : stage 0 = E₀ := by
  ext x
  constructor
  · rintro ⟨t, ⟨⟨j, lt, -⟩, -⟩ | ⟨-, rfl⟩⟩
    · exact absurd lt (Nat.not_lt_zero j)
    · exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, Or.inr ⟨fun ⟨j, lt, _⟩ => Nat.not_lt_zero j lt, rfl⟩⟩

theorem oriented_succ (i : ℕ) : oriented (i + 1) = oriented i ∪ {enum i} := by
  ext t
  constructor
  · rintro ⟨j, lt, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
    · exact Or.inl ⟨j, lt, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨j, lt, rfl⟩ | same)
    · exact ⟨j, Nat.lt_succ_of_lt lt, rfl⟩
    · exact ⟨i, Nat.lt_succ_self i, same.symm⟩

theorem pp_ne (t : GroundTerm sig) : p (p t) ≠ t :=
  ne_of_gt ((lt_p t).trans (lt_p (p t)))

/-- Two instances are one equation only when they are one instance. -/
theorem instance_eq {t u : GroundTerm sig} (same : (s(p (p t), t) : Sym2 _) = s(p (p u), u)) : t = u := by
  rcases Sym2.eq_iff.mp same with ⟨-, equal⟩ | ⟨first, second⟩
  · exact equal
  · rw [← first] at second
    have grow : t < p (p (p (p t))) :=
      ((lt_p t).trans (lt_p (p t))).trans ((lt_p (p (p t))).trans (lt_p (p (p (p t)))))
    rw [← second] at grow
    exact absurd grow (lt_irrefl t)

open Classical in
/-- **The run is a derivation**: stage `i + 1` orients the `i`-th instance, or idles. -/
theorem involution_derivation : Derivation stage where
  step i := by
    by_cases done : enum i ∈ oriented i
    · refine Or.inl ?_
      have same : oriented (i + 1) = oriented i := by
        rw [oriented_succ]
        exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr done)
      unfold stage
      rw [same]
    · refine Or.inr ⟨.orient (p (p (enum i))) (enum i), ?_⟩
      have more := oriented_succ i
      refine ⟨(lt_p _).trans (lt_p _), fun x member => ?_, fun x member => ?_, fun x member => ?_,
        fun x member notTaken => ?_, fun x member => ?_⟩
      · simp only [Rule.takes, Rule.reads, List.append_nil, List.mem_singleton] at member
        exact ⟨enum i, Or.inr ⟨done, member⟩⟩
      · simp [Rule.reads] at member
      · simp only [Rule.makes, List.mem_singleton] at member
        refine ⟨enum i, Or.inl ⟨?_, member⟩⟩
        rw [more]
        exact Or.inr rfl
      · obtain ⟨t, ⟨inO, rfl⟩ | ⟨outO, rfl⟩⟩ := member
        · exact ⟨t, Or.inl ⟨by rw [more]; exact Or.inl inO, rfl⟩⟩
        · refine ⟨t, Or.inr ⟨?_, rfl⟩⟩
          rw [more]
          rintro (inO | same)
          · exact outO inO
          · apply notTaken
            rw [Set.mem_singleton_iff.mp same]
            exact List.mem_singleton_self _
      · obtain ⟨t, ⟨inO, rfl⟩ | ⟨outO, rfl⟩⟩ := member
        · rw [more] at inO
          rcases inO with old | same
          · exact Or.inl ⟨t, Or.inl ⟨old, rfl⟩⟩
          · rw [Set.mem_singleton_iff.mp same]
            exact Or.inr (List.mem_singleton_self _)
        · rw [more] at outO
          exact Or.inl ⟨t, Or.inr ⟨fun inO => outO (Or.inl inO), rfl⟩⟩

theorem eventually_oriented (t : GroundTerm sig) : ∃ i, ∀ j, i ≤ j → t ∈ oriented j := by
  obtain ⟨i, rfl⟩ := enum_surjective t
  exact ⟨i + 1, fun j le => ⟨i, by omega, rfl⟩⟩

/-- **The persistent items are the rules `p(p(t)) → t`.** -/
theorem limit_involution : limit stage = Rinv := by
  ext x
  constructor
  · rintro ⟨i₀, persistent⟩
    obtain ⟨t, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := persistent i₀ le_rfl
    · exact ⟨t, rfl⟩
    · obtain ⟨i, oriented_after⟩ := eventually_oriented t
      obtain ⟨u, ⟨-, same⟩ | ⟨outU, same⟩⟩ := persistent (max i₀ i) (le_max_left _ _)
      · cases same
      · simp only [Item.eqn.injEq] at same
        rw [← instance_eq same] at outU
        exact absurd (oriented_after _ (le_max_right _ _)) outU
  · rintro ⟨t, rfl⟩
    obtain ⟨i, oriented_after⟩ := eventually_oriented t
    exact ⟨i, fun j le => ⟨t, Or.inl ⟨oriented_after j le, rfl⟩⟩⟩

/-- **Every critical pair is trivial**, so the run is fair. -/
theorem involution_fair : Fair stage := by
  intro l₁ r₁ l₂ r₂ d one two overlap
  rw [limit_involution] at one two
  obtain ⟨t₁, same₁⟩ := one
  obtain ⟨t₂, same₂⟩ := two
  simp only [Item.rule.injEq] at same₁ same₂
  rw [same₁.1, same₂.1] at overlap
  rw [same₁.2, same₂.2, same₂.1]
  have shift : p^[2] (p^[depth d] t₁) = p^[2] t₂ := by
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, ← ctx_fill]
    exact overlap
  have apart : d.fill t₁ = t₂ := by
    rw [ctx_fill]
    exact (p_injective.iterate 2) shift
  rw [apart]
  exact ⟨0, EqvGen.refl _⟩

theorem involution_noEquations : ∀ e, Item.eqn e ∉ limit stage := by
  intro e member
  rw [limit_involution] at member
  obtain ⟨t, same⟩ := member
  cases same

theorem start_decreasing : Decreasing (stage 0) := by
  intro l r member
  rw [stage_zero] at member
  obtain ⟨t, same⟩ := member
  cases same

/-- **`p(p(t)) → t` is convergent and decides the theory of the ground instances.** -/
theorem involution_convergent :
    Decreasing Rinv ∧ (∀ u, Acc (fun v u => Rw (rules Rinv) u v) u) ∧ Confluent (Rw (rules Rinv)) ∧
      ∀ s t, EqvGen (EqStep E₀) s t ↔ Joins (rules Rinv) s t := by
  have result := involution_derivation.convergent start_decreasing involution_fair involution_noEquations
  rw [limit_involution, stage_zero] at result
  exact result

/-! ## A word problem -/

theorem root_step (t : GroundTerm sig) : Rw (rules Rinv) (p (p t)) t := ⟨.hole, p (p t), t, ⟨t, rfl⟩, rfl, rfl⟩

/-- **`p⁵(a) ≈ p(a)` follows.** -/
theorem p5_p1 : EqvGen (EqStep E₀) (p^[5] a) (p a) :=
  (involution_convergent.2.2.2 _ _).mpr ⟨p a, .head (root_step (p (p (p a)))) (.single (root_step (p a))), .refl⟩

theorem below_rules {u : GroundTerm sig} (below : ∀ t, u < p (p t)) : IsNormal (Rw (rules Rinv)) u :=
  irreducible_of_below fun l r ⟨t, same⟩ => by
    simp only [Item.rule.injEq] at same
    rw [same.1]
    exact below t

/-- **`p(a) ≈ a` does not follow**: `p(a)` and `a` are distinct normal forms. -/
theorem p1_not_a : ¬ EqvGen (EqStep E₀) (p a) a := by
  intro derived
  obtain ⟨w, left, right⟩ := (involution_convergent.2.2.2 _ _).mp derived
  have one := (below_rules pa_lt_pp).reflTransGen_eq left
  have two := (below_rules fun t => a_lt_p (p t)).reflTransGen_eq right
  exact absurd (one.symm.trans two) (ne_of_gt (lt_p a))

#print axioms ctx_fill
#print axioms enum_surjective
#print axioms involution_derivation
#print axioms limit_involution
#print axioms involution_fair
#print axioms involution_convergent
#print axioms p5_p1
#print axioms p1_not_a

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion.Involution
