import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGround
import Mettapedia.Logic.Relation.Normalization

/-!
# Refutational completeness of ground superposition (Bachmair–Ganzinger)

A set of ground clauses that is saturated up to redundancy and does not contain the empty clause
has a model: the candidate model built from it (`candidate_models`, `satisfiable`). Equivalently,
an unsatisfiable saturated set contains the empty clause (`empty_mem_of_unsatisfiable`).

## Rewriting

* `Rw R` rewrites a rule's left side to its right side in a context; with a decreasing rule set it
  descends in the term ordering (`Rw.lt`).
* **A left-reduced system** (`LeftReduced`: one right side per left side, and no left side inside
  another) has joinable forks (`fork`). With termination, Newman's lemma
  (`Relation.confluent_of_accessible_forks`) makes it confluent, and joinability is a congruence
  (`joinCongruence`).
* Joinability of forks is confluence of one rewrite system: it completes a conflict between two
  rewrite steps. It is not independence of firings, which asks that each step survive the other
  (`Superposition.infer_independent`).
* **Joinability of small terms ignores large rules** (`joins_restrict`): reductions of terms below
  `m` never use a rule whose left side lies above `m`.

## The candidate model

Clauses are visited in increasing order. A clause `C = C' ∨ s ≈ t` **produces** the rule `s → t`
over the rules produced below it (`Produces`) when `s ≻ t`, `s ≈ t` is strictly maximal, `C` is
false, `s` is irreducible, and `C'` stays false once `s → t` is added. `below N C` is the set of rules
produced by the clauses of `N` smaller than `C` (defined by well-founded recursion, `below_iff`), and
`candidate N` is the set of all produced rules.

* The candidate system is left-reduced and decreasing (`candidate_leftReduced`).
* A productive clause is true (`produced_true`); the rest of a productive clause is false
  (`produced_rest_false`); a clause true at its own stage stays true (`persist`).
* **The main theorem** (`candidate_models`): take the least clause of `N` false in the candidate
  model. A maximal negative literal gives an equality resolution or a negative superposition, a
  maximal positive literal an equality factoring or a positive superposition, and the conclusion of
  each is true by saturation and minimality, which contradicts the falsity of the premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP
open _root_.Relation (ReflTransGen Join)

variable {sig : LPSignature}

/-! ## Rewriting with ground rules -/

section Rewriting

/-- **One rewrite step**: a rule's left side replaced by its right side in a context. -/
def Rw (R : GroundTerm sig → GroundTerm sig → Prop) (u v : GroundTerm sig) : Prop :=
  ∃ (c : Ctx sig) (l r : GroundTerm sig), R l r ∧ u = c.fill l ∧ v = c.fill r

/-- **Joinability**: both terms reduce to a common term. -/
def Joins (R : GroundTerm sig → GroundTerm sig → Prop) : GroundTerm sig → GroundTerm sig → Prop :=
  Join (ReflTransGen (Rw R))

variable {R R' : GroundTerm sig → GroundTerm sig → Prop}

theorem Rw.ctx {u v : GroundTerm sig} (step : Rw R u v) (c : Ctx sig) : Rw R (c.fill u) (c.fill v) := by
  obtain ⟨d, l, r, rule, rfl, rfl⟩ := step
  exact ⟨c.comp d, l, r, rule, (Ctx.fill_comp c d l).symm, (Ctx.fill_comp c d r).symm⟩

theorem Rw.root {l r : GroundTerm sig} (rule : R l r) : Rw R l r := ⟨.hole, l, r, rule, rfl, rfl⟩

theorem Rw.mono (sub : ∀ l r, R l r → R' l r) {u v : GroundTerm sig} (step : Rw R u v) : Rw R' u v := by
  obtain ⟨c, l, r, rule, rfl, rfl⟩ := step
  exact ⟨c, l, r, sub l r rule, rfl, rfl⟩

theorem Joins.mono (sub : ∀ l r, R l r → R' l r) {u v : GroundTerm sig} (join : Joins R u v) :
    Joins R' u v := by
  obtain ⟨w, left, right⟩ := join
  exact ⟨w, left.lift id fun _ _ step => Rw.mono sub step, right.lift id fun _ _ step => Rw.mono sub step⟩

theorem Joins.refl (u : GroundTerm sig) : Joins R u u := ⟨u, .refl, .refl⟩

theorem Joins.symm {u v : GroundTerm sig} (join : Joins R u v) : Joins R v u := by
  obtain ⟨w, left, right⟩ := join
  exact ⟨w, right, left⟩

theorem Joins.ctx {u v : GroundTerm sig} (join : Joins R u v) (c : Ctx sig) :
    Joins R (c.fill u) (c.fill v) := by
  obtain ⟨w, left, right⟩ := join
  exact ⟨c.fill w, left.lift c.fill (fun _ _ step => step.ctx c),
    right.lift c.fill (fun _ _ step => step.ctx c)⟩

theorem joins_of_rule {l r : GroundTerm sig} (rule : R l r) : Joins R l r :=
  ⟨r, .single (Rw.root rule), .refl⟩

/-- **A left-reduced system**: one right side per left side, and no left side occurs inside another. -/
structure LeftReduced (R : GroundTerm sig → GroundTerm sig → Prop) : Prop where
  unique : ∀ l r r', R l r → R l r' → r = r'
  inner : ∀ (l r l' r' : GroundTerm sig) (c : Ctx sig), R l r → R l' r' → c.fill l' = l → c = .hole

/-- **Forks of a left-reduced system are joinable.** -/
theorem fork (lr : LeftReduced R) : ∀ (c₁ c₂ : Ctx sig) {l₁ r₁ l₂ r₂ : GroundTerm sig},
    R l₁ r₁ → R l₂ r₂ → c₁.fill l₁ = c₂.fill l₂ → Joins R (c₁.fill r₁) (c₂.fill r₂)
  | .hole, .hole, l₁, r₁, l₂, r₂, rule₁, rule₂, same => by
      simp only [Ctx.fill_hole] at same ⊢
      subst same
      rw [lr.unique _ _ _ rule₁ rule₂]
      exact Joins.refl _
  | .hole, .app f args i inner, l₁, r₁, l₂, r₂, rule₁, rule₂, same => by
      exact absurd (lr.inner l₁ r₁ l₂ r₂ (.app f args i inner) rule₁ rule₂ same.symm) (by simp)
  | .app f args i inner, .hole, l₁, r₁, l₂, r₂, rule₁, rule₂, same => by
      exact absurd (lr.inner l₂ r₂ l₁ r₁ (.app f args i inner) rule₂ rule₁ same) (by simp)
  | .app f args i inner, .app g args' j inner', l₁, r₁, l₂, r₂, rule₁, rule₂, same => by
      obtain ⟨rfl, hargs⟩ := GroundTerm.app.inj same
      have equal := eq_of_heq hargs
      have off : ∀ k, k ≠ i → k ≠ j → args k = args' k := fun k hi hj => by
        have at_k := congrFun equal k
        rwa [Function.update_of_ne hi, Function.update_of_ne hj] at at_k
      by_cases hij : i = j
      · subst hij
        have at_i := congrFun equal i
        rw [Function.update_self, Function.update_self] at at_i
        have join := fork lr inner inner' rule₁ rule₂ at_i
        have args_eq : Function.update args' i (inner'.fill r₂) =
            Function.update args i (inner'.fill r₂) := by
          funext k
          by_cases hk : k = i
          · subst hk
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hk, Function.update_of_ne hk]
            exact (off k hk hk).symm
        show Joins R (GroundTerm.app f (Function.update args i (inner.fill r₁)))
          (GroundTerm.app f (Function.update args' i (inner'.fill r₂)))
        rw [args_eq]
        exact join.ctx (.app f args i .hole)
      · have at_i := congrFun equal i
        rw [Function.update_self, Function.update_of_ne hij] at at_i
        have at_j := congrFun equal j
        rw [Function.update_of_ne (Ne.symm hij), Function.update_self] at at_j
        let common := Function.update (Function.update args i (inner.fill r₁)) j (inner'.fill r₂)
        refine ⟨GroundTerm.app f common, .single ?_, .single ?_⟩
        · refine ⟨.app f (Function.update args i (inner.fill r₁)) j inner', l₂, r₂, rule₂, ?_, rfl⟩
          show GroundTerm.app f (Function.update args i (inner.fill r₁)) =
            GroundTerm.app f (Function.update (Function.update args i (inner.fill r₁)) j (inner'.fill l₂))
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk
            rw [Function.update_self, Function.update_of_ne (Ne.symm hij)]
            exact at_j
          · rw [Function.update_of_ne hk]
        · refine ⟨.app f (Function.update args' j (inner'.fill r₂)) i inner, l₁, r₁, rule₁, ?_, ?_⟩
          · show GroundTerm.app f (Function.update args' j (inner'.fill r₂)) =
              GroundTerm.app f (Function.update (Function.update args' j (inner'.fill r₂)) i (inner.fill l₁))
            congr 1
            funext k
            by_cases hk : k = i
            · subst hk
              rw [Function.update_self, Function.update_of_ne hij]
              exact at_i.symm
            · rw [Function.update_of_ne hk]
          · show GroundTerm.app f common =
              GroundTerm.app f (Function.update (Function.update args' j (inner'.fill r₂)) i (inner.fill r₁))
            congr 1
            funext k
            by_cases hk : k = i
            · subst hk
              simp only [common]
              rw [Function.update_of_ne hij, Function.update_self, Function.update_self]
            · by_cases hk' : k = j
              · subst hk'
                simp only [common]
                rw [Function.update_self, Function.update_of_ne hk, Function.update_self]
              · simp only [common]
                rw [Function.update_of_ne hk', Function.update_of_ne hk, Function.update_of_ne hk,
                  Function.update_of_ne hk']
                exact off k hk hk'

variable [LinearOrder (GroundTerm sig)] [GroundSimplification sig]

/-- **A decreasing rule set rewrites downward.** -/
theorem Rw.lt (decreasing : ∀ l r, R l r → r < l) {u v : GroundTerm sig} (step : Rw R u v) : v < u := by
  obtain ⟨c, l, r, rule, rfl, rfl⟩ := step
  exact c.fill_lt_fill (decreasing l r rule)

theorem steps_le (decreasing : ∀ l r, R l r → r < l) {u v : GroundTerm sig}
    (steps : ReflTransGen (Rw R) u v) : v ≤ u := by
  induction steps with
  | refl => exact le_rfl
  | tail _ step ih => exact (step.lt decreasing).le.trans ih

/-- **Joinability of small terms ignores large rules**: with `R ⊆ R'` and every rule of `R'` outside
`R` having its left side above `m`, reductions from a term below `m` stay in `R`. -/
theorem steps_restrict (decreasing : ∀ l r, R' l r → r < l)
    {m : GroundTerm sig} (high : ∀ l r, R' l r → ¬ R l r → m < l) {u w : GroundTerm sig}
    (steps : ReflTransGen (Rw R') u w) (small : u ≤ m) : ReflTransGen (Rw R) u w ∧ w ≤ u := by
  induction steps with
  | refl => exact ⟨.refl, le_rfl⟩
  | tail _ step ih =>
      obtain ⟨before, low⟩ := ih
      obtain ⟨c, l, r, rule, rfl, rfl⟩ := step
      have inR : R l r := by
        by_contra out
        exact lt_irrefl m ((high l r rule out).trans_le ((c.le_fill l).trans (low.trans small)))
      exact ⟨before.tail ⟨c, l, r, inR, rfl, rfl⟩, ((c.fill_lt_fill (decreasing l r rule)).le).trans low⟩

theorem joins_restrict (decreasing : ∀ l r, R' l r → r < l)
    {m : GroundTerm sig} (high : ∀ l r, R' l r → ¬ R l r → m < l) {u v : GroundTerm sig}
    (hu : u ≤ m) (hv : v ≤ m) (join : Joins R' u v) : Joins R u v := by
  obtain ⟨w, left, right⟩ := join
  exact ⟨w, (steps_restrict decreasing high left hu).1, (steps_restrict decreasing high right hv).1⟩

variable [WellFoundedLT (GroundTerm sig)]

/-- **Newman's lemma for a left-reduced, decreasing system**: it is confluent. -/
theorem confluent (lr : LeftReduced R) (decreasing : ∀ l r, R l r → r < l) :
    Mettapedia.Logic.Relation.Confluent (Rw R) :=
  Mettapedia.Logic.Relation.confluent_of_accessible_forks
    (fun s => Subrelation.accessible (fun {_ _} step => Rw.lt decreasing step) (wellFounded_lt.apply s))
    (fun _ _ _ first second => by
      obtain ⟨c₁, l₁, r₁, rule₁, rfl, rfl⟩ := first
      obtain ⟨c₂, l₂, r₂, rule₂, same, rfl⟩ := second
      exact fork lr c₁ c₂ rule₁ rule₂ same)

/-- **Joinability in a left-reduced, decreasing system is an equality interpretation.** -/
def joinCongruence (lr : LeftReduced R) (decreasing : ∀ l r, R l r → r < l) : Congruence sig where
  rel := Joins R
  equivalence := _root_.Relation.equivalence_join (confluent lr decreasing)
  compatible c _ _ join := join.ctx c

end Rewriting

/-! ## The candidate model -/

section Candidate

variable [LinearOrder (GroundTerm sig)]

/-- **`C` produces the rule `s → t` over the rules `R`** (Bachmair–Ganzinger). -/
structure Produces (R : GroundTerm sig → GroundTerm sig → Prop) (C : Clause (GroundTerm sig))
    (s t : GroundTerm sig) : Prop where
  decreasing : t < s
  mem : Lit.pos s t decreasing.le ∈ C
  strict : ∀ M ∈ C.erase (Lit.pos s t decreasing.le), M < Lit.pos s t decreasing.le
  falseIn : ¬ Models (Joins R) C
  irreducible : ∀ v, ¬ Rw R s v
  rest : ¬ Models (Joins fun a b => R a b ∨ (a = s ∧ b = t)) (C.erase (Lit.pos s t decreasing.le))

theorem Produces.max {R : GroundTerm sig → GroundTerm sig → Prop} {C : Clause (GroundTerm sig)}
    {s t : GroundTerm sig} (p : Produces R C s t) : ∀ M ∈ C, M ≤ Lit.pos s t p.decreasing.le := by
  intro M member
  by_cases same : M = Lit.pos s t p.decreasing.le
  · exact same.le
  · exact (p.strict M ((Multiset.mem_erase_of_ne same).mpr member)).le

/-- The produced rule is unique to the clause. -/
theorem Produces.unique {R R' : GroundTerm sig → GroundTerm sig → Prop} {C : Clause (GroundTerm sig)}
    {s t s' t' : GroundTerm sig} (p : Produces R C s t) (q : Produces R' C s' t') : s = s' ∧ t = t' := by
  have one := p.max _ q.mem
  have two := q.max _ p.mem
  have same := le_antisymm one two
  exact ⟨(congrArg Lit.lhs same).symm, (congrArg Lit.rhs same).symm⟩

/-- Every term of a productive clause lies at or below its left side. -/
theorem Produces.lhs_le {R : GroundTerm sig → GroundTerm sig → Prop} {C : Clause (GroundTerm sig)}
    {s t : GroundTerm sig} (p : Produces R C s t) {M : Lit (GroundTerm sig)} (member : M ∈ C) :
    M.lhs ≤ s :=
  Lit.lhs_le_of_le (p.max M member)

/-- Literals of a smaller clause lie below the produced literal of a larger productive clause. -/
theorem le_pos_of_lt {C D : Clause (GroundTerm sig)} (lt : ClauseLT C D)
    {R : GroundTerm sig → GroundTerm sig → Prop} {l r : GroundTerm sig} (p : Produces R D l r) :
    ∀ M ∈ C, M ≤ Lit.pos l r p.decreasing.le := by
  intro M member
  obtain ⟨M', inD, le⟩ := dm_le lt member
  exact le.trans (p.max M' inD)

variable [WellFoundedLT (GroundTerm sig)]

variable (N : Set (Clause (GroundTerm sig)))

/-- **The rules produced below `C`** by the clauses of `N`. -/
noncomputable def below : Clause (GroundTerm sig) → GroundTerm sig → GroundTerm sig → Prop :=
  clauseLT_wf.fix fun C below l r => ∃ D ∈ N, ∃ h : ClauseLT D C, Produces (below D h) D l r

theorem below_iff (C : Clause (GroundTerm sig)) (l r : GroundTerm sig) :
    below N C l r ↔ ∃ D ∈ N, ClauseLT D C ∧ Produces (below N D) D l r := by
  unfold below
  rw [WellFounded.fix_eq]
  simp only [exists_prop]

/-- A rule produced by a clause of `N`. -/
def produced (D : Clause (GroundTerm sig)) (l r : GroundTerm sig) : Prop :=
  D ∈ N ∧ Produces (below N D) D l r

/-- **The candidate rewrite system**: every rule produced by a clause of `N`. -/
def candidate (l r : GroundTerm sig) : Prop := ∃ D, produced N D l r

variable {N}

theorem below_candidate {C : Clause (GroundTerm sig)} {l r : GroundTerm sig} (rule : below N C l r) :
    candidate N l r := by
  obtain ⟨D, member, -, p⟩ := (below_iff N C l r).mp rule
  exact ⟨D, member, p⟩

theorem candidate_decreasing {l r : GroundTerm sig} (rule : candidate N l r) : r < l := by
  obtain ⟨D, -, p⟩ := rule
  exact p.decreasing

theorem below_decreasing {C : Clause (GroundTerm sig)} {l r : GroundTerm sig} (rule : below N C l r) :
    r < l :=
  candidate_decreasing (below_candidate rule)

/-- **Left sides grow with the producing clause.** -/
theorem produced_lhs_lt {D D' : Clause (GroundTerm sig)} {l r l' r' : GroundTerm sig}
    (one : produced N D l r) (two : produced N D' l' r') (lt : ClauseLT D D') : l < l' := by
  have le : l ≤ l' := Lit.lhs_le_of_le (le_pos_of_lt lt two.2 _ one.2.mem)
  refine lt_of_le_of_ne le fun same => ?_
  subst same
  exact two.2.irreducible r (Rw.root ((below_iff N D' l r).mpr ⟨D, one.1, lt, one.2⟩))

variable [GroundSimplification sig]

/-- **The candidate system is left-reduced.** -/
theorem candidate_leftReduced : LeftReduced (candidate N) where
  unique := by
    rintro l r r' ⟨D, one⟩ ⟨D', two⟩
    rcases clauseLT_trichotomous D D' with lt | rfl | lt
    · exact absurd (produced_lhs_lt one two lt) (lt_irrefl l)
    · exact (one.2.unique two.2).2
    · exact absurd (produced_lhs_lt two one lt) (lt_irrefl l)
  inner := by
    rintro l r l' r' c ⟨D, one⟩ ⟨D', two⟩ filled
    by_contra proper
    have inside : l' < l := filled ▸ c.lt_fill proper l'
    rcases clauseLT_trichotomous D' D with lt | rfl | lt
    · apply one.2.irreducible (c.fill r')
      rw [← filled]
      exact ⟨c, l', r', (below_iff N D l' r').mpr ⟨D', two.1, lt, two.2⟩, rfl, rfl⟩
    · exact absurd (one.2.unique two.2).1 (ne_of_gt inside)
    · exact absurd (produced_lhs_lt one two lt) (not_lt.mpr inside.le)

/-- **The candidate interpretation**: joinability in the candidate system. -/
def candidateModel (N : Set (Clause (GroundTerm sig))) : Congruence sig :=
  joinCongruence (candidate_leftReduced (N := N)) fun _ _ rule => candidate_decreasing (N := N) rule

theorem candidateModel_rel (N : Set (Clause (GroundTerm sig))) :
    (candidateModel N).rel = Joins (candidate N) := rfl

omit [GroundSimplification sig] in
/-- **A productive clause is true.** -/
theorem produced_true {C : Clause (GroundTerm sig)} {s t : GroundTerm sig} (p : produced N C s t) :
    Models (Joins (candidate N)) C :=
  ⟨_, p.2.mem, (Lit.holds_of_positive rfl).mpr (joins_of_rule ⟨C, p⟩)⟩

/-- **The rest of a productive clause is false.** -/
theorem produced_rest_false {D : Clause (GroundTerm sig)} {l r : GroundTerm sig} (p : produced N D l r) :
    ∀ M ∈ D.erase (Lit.pos l r p.2.decreasing.le), ¬ M.Holds (Joins (candidate N)) := by
  intro M member holds
  let R0 : GroundTerm sig → GroundTerm sig → Prop := fun a b => below N D a b ∨ (a = l ∧ b = r)
  have sub : ∀ a b, R0 a b → candidate N a b := by
    rintro a b (rule | ⟨rfl, rfl⟩)
    · exact below_candidate rule
    · exact ⟨D, p⟩
  have high : ∀ a b, candidate N a b → ¬ R0 a b → l < a := by
    rintro a b ⟨D'', q⟩ out
    rcases clauseLT_trichotomous D'' D with lt | rfl | lt
    · exact absurd (Or.inl ((below_iff N D a b).mpr ⟨D'', q.1, lt, q.2⟩)) out
    · obtain ⟨rfl, rfl⟩ := q.2.unique p.2
      exact absurd (Or.inr ⟨rfl, rfl⟩) out
    · exact produced_lhs_lt p q lt
  have false0 : ¬ M.Holds (Joins R0) := fun h => p.2.rest ⟨M, member, h⟩
  have inD := Multiset.mem_of_mem_erase member
  cases sign : M.negative
  · rw [Lit.holds_of_positive sign] at holds
    apply false0
    rw [Lit.holds_of_positive sign]
    exact joins_restrict (fun _ _ rule => candidate_decreasing rule) high (p.2.lhs_le inD)
      (M.oriented.trans (p.2.lhs_le inD)) holds
  · rw [Lit.holds_of_negative sign] at holds
    apply false0
    rw [Lit.holds_of_negative sign]
    exact fun join => holds (join.mono sub)

/-- The rules at the stage of `C`: those produced below it and the one it produces. -/
def atStage (N : Set (Clause (GroundTerm sig))) (C : Clause (GroundTerm sig)) (l r : GroundTerm sig) :
    Prop :=
  below N C l r ∨ produced N C l r

/-- **A clause true at its own stage stays true.** -/
theorem persist {C : Clause (GroundTerm sig)} (holds : Models (Joins (atStage N C)) C) :
    Models (Joins (candidate N)) C := by
  obtain ⟨L, member, holds⟩ := holds
  have sub : ∀ a b, atStage N C a b → candidate N a b := by
    rintro a b (rule | rule)
    · exact below_candidate rule
    · exact ⟨C, rule⟩
  refine ⟨L, member, ?_⟩
  cases sign : L.negative
  · rw [Lit.holds_of_positive sign] at holds ⊢
    exact holds.mono sub
  · rw [Lit.holds_of_negative sign] at holds ⊢
    intro join
    apply holds
    have high : ∀ a b, candidate N a b → ¬ atStage N C a b → L.lhs < a := by
      rintro a b ⟨D, q⟩ out
      rcases clauseLT_trichotomous D C with lt | rfl | lt
      · exact absurd (Or.inl ((below_iff N C a b).mpr ⟨D, q.1, lt, q.2⟩)) out
      · exact absurd (Or.inr q) out
      · exact Lit.lhs_lt_of_negative_le_pos (le_pos_of_lt lt q.2 L member) sign
    exact joins_restrict (fun _ _ rule => candidate_decreasing rule) high le_rfl L.oriented join

/-! ## The main theorem -/

/-- **Refutational completeness of ground superposition (Bachmair–Ganzinger).** A set of ground
clauses that is saturated up to redundancy and does not contain the empty clause is true in its
candidate model. -/
theorem candidate_models (saturated : Saturated N) (noEmpty : (0 : Clause (GroundTerm sig)) ∉ N) :
    ∀ C ∈ N, Models (Joins (candidate N)) C := by
  by_contra exists_false
  push Not at exists_false
  obtain ⟨C, ⟨inN, falseC⟩, minimal⟩ :=
    clauseLT_wf.has_min {C | C ∈ N ∧ ¬ Models (Joins (candidate N)) C} exists_false
  have symm : ∀ a b, Joins (candidate N) a b → Joins (candidate N) b a := fun _ _ h => h.symm
  have trans : ∀ {a b c}, Joins (candidate N) a b → Joins (candidate N) b c → Joins (candidate N) a c :=
    fun one two => (candidateModel_rel N ▸ (candidateModel N).equivalence).trans one two
  -- conclusions of redundant inferences with main premise `C` are true
  have redundant_true : ∀ E, RedundantInference N C E → Models (Joins (candidate N)) E := by
    intro E redundant
    have holds := redundant (candidateModel N) fun D ⟨member, lt⟩ => by
      rw [candidateModel_rel]
      by_contra falseD
      exact minimal D ⟨member, falseD⟩ lt
    rwa [candidateModel_rel] at holds
  have inferred_true : ∀ side E, Inference side C E → (∀ D ∈ side, D ∈ N) →
      Models (Joins (candidate N)) E :=
    fun side E inference sides => redundant_true E (saturated side C E inference sides inN)
  -- `C` is not productive, so it is false at its own stage
  have notProduced : ∀ s t, ¬ Produces (below N C) C s t :=
    fun s t p => falseC (produced_true ⟨inN, p⟩)
  have falseBelow : ¬ Models (Joins (below N C)) C := by
    rintro ⟨L, member, holdsL⟩
    apply falseC
    apply persist
    refine ⟨L, member, ?_⟩
    cases sign : L.negative
    · rw [Lit.holds_of_positive sign] at holdsL ⊢
      exact holdsL.mono fun a b rule => Or.inl rule
    · rw [Lit.holds_of_negative sign] at holdsL ⊢
      intro join
      apply holdsL
      refine Joins.mono (fun a b rule => ?_) join
      rcases rule with rule | rule
      · exact rule
      · exact absurd rule.2 (notProduced a b)
  have literal_false : ∀ M ∈ C, ¬ M.Holds (Joins (candidate N)) := fun M member h => falseC ⟨M, member, h⟩
  -- the maximal literal
  have nonempty : C ≠ 0 := fun zero => noEmpty (zero ▸ inN)
  obtain ⟨L, inC, top'⟩ := Finset.exists_max_image C.toFinset id
    (Multiset.toFinset_nonempty.mpr nonempty)
  rw [Multiset.mem_toFinset] at inC
  have top : ∀ M ∈ C, M ≤ L := fun M member => top' M (Multiset.mem_toFinset.mpr member)
  have decompose : L ::ₘ C.erase L = C := Multiset.cons_erase inC
  have rest_le : ∀ M ∈ C.erase L, M ≤ L := fun M member => top M (Multiset.mem_of_mem_erase member)
  have rest_false : ∀ M ∈ C.erase L, ¬ M.Holds (Joins (candidate N)) :=
    fun M member => literal_false M (Multiset.mem_of_mem_erase member)
  -- a rule of `below N C` rewriting the larger side of `L`
  have rewritable : ∀ {v}, Rw (below N C) L.lhs v → ∃ (c : Ctx sig) (l r : GroundTerm sig) (D : Clause (GroundTerm sig)),
      L.lhs = c.fill l ∧ D ∈ N ∧ ClauseLT D C ∧ Produces (below N D) D l r := by
    rintro v ⟨c, l, r, rule, same, -⟩
    obtain ⟨D, member, lt, p⟩ := (below_iff N C l r).mp rule
    exact ⟨c, l, r, D, same, member, lt, p⟩
  cases sign : L.negative
  · -- a maximal positive literal
    have notJoined : ¬ Joins (candidate N) L.lhs L.rhs := fun join =>
      literal_false L inC ((Lit.holds_of_positive sign).mpr join)
    have strict : L.rhs < L.lhs := lt_of_le_of_ne L.oriented fun same => notJoined (same ▸ Joins.refl _)
    by_cases strictMax : ∀ M ∈ C.erase L, M < L
    · by_cases reducible : ∃ v, Rw (below N C) L.lhs v
      · -- positive superposition
        obtain ⟨v, step⟩ := reducible
        obtain ⟨c, l, r, D, larger, inD, lt, p⟩ := rewritable step
        have sideDecompose : Lit.pos l r p.decreasing.le ::ₘ D.erase (Lit.pos l r p.decreasing.le) = D :=
          Multiset.cons_erase p.mem
        have smaller : Lit.pos l r p.decreasing.le < L := by
          obtain ⟨M, member, le⟩ := dm_le lt p.mem
          refine lt_of_le_of_ne (le.trans (top M member)) fun same => ?_
          apply falseBelow
          refine ⟨L, inC, (Lit.holds_of_positive sign).mpr ?_⟩
          rw [← same]
          exact joins_of_rule ((below_iff N C l r).mpr ⟨D, inD, lt, p⟩)
        have inference := Inference.posSup (D.erase (Lit.pos l r p.decreasing.le)) (C.erase L) L c
          p.decreasing p.strict sign larger strict strictMax smaller
        rw [decompose, sideDecompose] at inference
        have concl := inferred_true _ _ inference (fun X member => by
          rw [Option.mem_def, Option.some.injEq] at member
          exact member ▸ inD)
        rcases models_cons.mp concl with made | others
        · rw [Lit.holds_make symm] at made
          apply notJoined
          rw [larger]
          have rule : candidate N l r := below_candidate ((below_iff N C l r).mpr ⟨D, inD, lt, p⟩)
          exact trans ((joins_of_rule rule).ctx c) made
        · rcases models_add.mp others with ⟨M, member, holds⟩ | ⟨M, member, holds⟩
          · exact produced_rest_false ⟨inD, p⟩ M member holds
          · exact rest_false M member holds
      · -- `L.lhs` is irreducible: equality factoring, unless `C` would be productive
        push Not at reducible
        have restTrue : Models (Joins fun a b => below N C a b ∨ (a = L.lhs ∧ b = L.rhs)) (C.erase L) := by
          by_contra restFalse
          have same : L = Lit.pos L.lhs L.rhs strict.le := Lit.ext rfl sign rfl
          apply notProduced L.lhs L.rhs
          refine ⟨strict, same ▸ inC, fun M member => ?_, falseBelow, reducible, ?_⟩
          · rw [← same] at member ⊢
            exact strictMax M member
          · rw [← same]
            exact restFalse
        obtain ⟨M, member, holds⟩ := restTrue
        let R1 : GroundTerm sig → GroundTerm sig → Prop := fun a b => below N C a b ∨ (a = L.lhs ∧ b = L.rhs)
        have sub1 : ∀ a b, below N C a b → R1 a b := fun a b rule => Or.inl rule
        have dec1 : ∀ a b, R1 a b → b < a := by
          rintro a b (rule | ⟨rfl, rfl⟩)
          · exact below_decreasing rule
          · exact strict
        have high1 : ∀ a b, R1 a b → ¬ below N C a b → L.lhs ≤ a := by
          rintro a b (rule | ⟨rfl, rfl⟩) out
          · exact absurd rule out
          · exact le_rfl
        have M_lt : M < L := strictMax M member
        cases signM : M.negative
        · rw [Lit.holds_of_positive signM] at holds
          rcases Lit.lt_iff.mp M_lt with small | ⟨sameLhs, signs⟩
          · -- a smaller literal: it would hold below `C`
            apply falseBelow
            refine ⟨M, Multiset.mem_of_mem_erase member, (Lit.holds_of_positive signM).mpr ?_⟩
            exact joins_restrict dec1 (fun a b rule out => small.trans_le (high1 a b rule out))
              le_rfl M.oriented holds
          · -- the same larger side: equality factoring
            have rhsLt : M.rhs < L.rhs := by
              rcases signs with signs | ⟨-, small⟩
              · rw [signM, sign] at signs
                exact absurd signs (by decide)
              · exact small
            obtain ⟨w, left, right⟩ := holds
            rw [sameLhs] at left
            rcases left.cases_head with stay | ⟨x, first, rest⟩
            · have := steps_le dec1 right
              rw [← stay] at this
              exact absurd this (not_le.mpr (rhsLt.trans strict))
            · obtain ⟨c, l, r, rule, at_root, rfl⟩ := first
              rcases rule with rule | ⟨rfl, rfl⟩
              · exact reducible _ ⟨c, l, r, rule, at_root, rfl⟩
              · have hole := Ctx.eq_hole_of_fill_eq c at_root.symm
                subst hole
                have high' : ∀ a b, R1 a b → ¬ below N C a b → L.rhs < a := fun a b rule out =>
                  strict.trans_le (high1 a b rule out)
                have joined : Joins (below N C) L.rhs M.rhs :=
                  joins_restrict dec1 high' le_rfl rhsLt.le ⟨w, rest, right⟩
                have restDecompose : M ::ₘ (C.erase L).erase M = C.erase L := Multiset.cons_erase member
                have inference := Inference.eqFact ((C.erase L).erase M) L M sign signM sameLhs strict
                  (by rw [restDecompose]; exact rest_le)
                rw [restDecompose, decompose] at inference
                have concl := inferred_true _ _ inference (fun X member => by simp at member)
                rcases models_cons.mp concl with made | others
                · rw [Lit.holds_make symm] at made
                  exact made (joined.mono fun a b rule => below_candidate rule)
                · obtain ⟨M', member', holds'⟩ := others
                  exact rest_false M' member' holds'
        · -- a negative literal true after adding `L` is true before
          rw [Lit.holds_of_negative signM] at holds
          apply falseBelow
          refine ⟨M, Multiset.mem_of_mem_erase member, (Lit.holds_of_negative signM).mpr ?_⟩
          exact fun join => holds (join.mono sub1)
    · -- `L` is not strictly maximal: equality factoring with a copy of itself
      push Not at strictMax
      obtain ⟨M, member, notLt⟩ := strictMax
      have same : M = L := le_antisymm (rest_le M member) notLt
      have again : L ∈ C.erase L := same ▸ member
      have restDecompose : L ::ₘ (C.erase L).erase L = C.erase L := Multiset.cons_erase again
      have inference := Inference.eqFact ((C.erase L).erase L) L L sign sign rfl strict
        (by rw [restDecompose]; exact rest_le)
      rw [restDecompose, decompose] at inference
      have concl := inferred_true _ _ inference (fun X member => by simp at member)
      rcases models_cons.mp concl with made | others
      · rw [Lit.holds_make symm] at made
        exact made (Joins.refl _)
      · obtain ⟨M', member', holds'⟩ := others
        exact rest_false M' member' holds'
  · -- a maximal negative literal
    have joined : Joins (candidate N) L.lhs L.rhs := by
      by_contra notJoined
      exact literal_false L inC ((Lit.holds_of_negative sign).mpr notJoined)
    have high : ∀ a b, candidate N a b → ¬ below N C a b → L.lhs < a := by
      rintro a b ⟨D, q⟩ out
      rcases clauseLT_trichotomous D C with lt | rfl | lt
      · exact absurd ((below_iff N C a b).mpr ⟨D, q.1, lt, q.2⟩) out
      · exact absurd q.2 (notProduced a b)
      · exact Lit.lhs_lt_of_negative_le_pos (le_pos_of_lt lt q.2 L inC) sign
    have joinedBelow : Joins (below N C) L.lhs L.rhs :=
      joins_restrict (fun _ _ rule => candidate_decreasing rule)
        high le_rfl L.oriented joined
    by_cases trivial : L.rhs = L.lhs
    · -- equality resolution
      have inference := Inference.eqRes (C.erase L) L sign trivial rest_le
      rw [decompose] at inference
      obtain ⟨M, member, holds⟩ := inferred_true _ _ inference (fun X member => by simp at member)
      exact rest_false M member holds
    · -- negative superposition
      have strict : L.rhs < L.lhs := lt_of_le_of_ne L.oriented trivial
      have reducible : ∃ v, Rw (below N C) L.lhs v := by
        by_contra irreducible
        push Not at irreducible
        obtain ⟨w, left, right⟩ := joinedBelow
        rcases left.cases_head with stay | ⟨x, first, -⟩
        · have := steps_le (fun _ _ rule => below_decreasing rule) right
          rw [← stay] at this
          exact absurd this (not_le.mpr strict)
        · exact irreducible x first
      obtain ⟨v, step⟩ := reducible
      obtain ⟨c, l, r, D, larger, inD, lt, p⟩ := rewritable step
      have sideDecompose : Lit.pos l r p.decreasing.le ::ₘ D.erase (Lit.pos l r p.decreasing.le) = D :=
        Multiset.cons_erase p.mem
      have inference := Inference.negSup (D.erase (Lit.pos l r p.decreasing.le)) (C.erase L) L c
        p.decreasing p.strict sign larger strict rest_le
      rw [decompose, sideDecompose] at inference
      have concl := inferred_true _ _ inference (fun X member => by
        rw [Option.mem_def, Option.some.injEq] at member
        exact member ▸ inD)
      rcases models_cons.mp concl with made | others
      · rw [Lit.holds_make symm] at made
        apply made
        have rule : candidate N l r := below_candidate ((below_iff N C l r).mpr ⟨D, inD, lt, p⟩)
        have down : Joins (candidate N) (c.fill l) (c.fill r) := Joins.ctx (joins_of_rule rule) c
        rw [← larger] at down
        exact trans down.symm joined
      · rcases models_add.mp others with ⟨M, member, holds⟩ | ⟨M, member, holds⟩
        · exact produced_rest_false ⟨inD, p⟩ M member holds
        · exact rest_false M member holds

/-- **A saturated set without the empty clause is satisfiable.** -/
theorem satisfiable (saturated : Saturated N) (noEmpty : (0 : Clause (GroundTerm sig)) ∉ N) :
    ∃ I : Congruence sig, ∀ C ∈ N, Models I.rel C :=
  ⟨candidateModel N, by rw [candidateModel_rel]; exact candidate_models saturated noEmpty⟩

/-- **Refutational completeness**: an unsatisfiable saturated set contains the empty clause. -/
theorem empty_mem_of_unsatisfiable (saturated : Saturated N)
    (unsatisfiable : ¬ ∃ I : Congruence sig, ∀ C ∈ N, Models I.rel C) :
    (0 : Clause (GroundTerm sig)) ∈ N := by
  by_contra noEmpty
  exact unsatisfiable (satisfiable saturated noEmpty)

end Candidate

#print axioms fork
#print axioms steps_restrict
#print axioms joins_restrict
#print axioms confluent
#print axioms below_iff
#print axioms Produces.unique
#print axioms produced_lhs_lt
#print axioms candidate_leftReduced
#print axioms produced_true
#print axioms produced_rest_false
#print axioms persist
#print axioms candidate_models
#print axioms satisfiable
#print axioms empty_mem_of_unsatisfiable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
