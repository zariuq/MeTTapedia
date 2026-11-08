import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedSource

/-!
# The natural most general unifiers of the machine's firings

A firing's admission and result read the knowledge through any most general unifier of its
selected problem (`ProgramEquationsOpen.ofire_at`). For the frame-stack machine two are natural.

* **The matcher** (`matcher`, `matcher_isMGU`): when a row is an instance `p.fill vals` of a
  pattern `p` copied at a fresh scope, binding each pattern variable to its value is a most general
  unifier. A row variable met by a pattern variable stays where it is: the matcher binds only the
  fresh variables, so the rest of the configuration is untouched (`matcher_fixes`).
* **Extension by a fresh variable** (`isMGU_extend`): a most general unifier of a problem, extended
  by binding a variable that occurs nowhere in it to the image of a term, is a most general unifier
  of the problem with that equation added. A call's continuation is carried this way.
* **Equal sides** (`isMGU_id_of_eq`): a problem whose sides are equal has the identity as most
  general unifier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-! ## Filling a pattern with values -/

/-- The instance of a pattern whose `x`-th variable is the `x`-th value. -/
def Pat.fill (vals : List Tm) : Pat → Tm
  | .var x => vals.getD x (.const 0)
  | .sym k => .const k
  | .cell a b => node (Pat.fill vals a) (Pat.fill vals b)

theorem getD_mem {vals : List Tm} {x : ℕ} (lt : x < vals.length) (d : Tm) : vals.getD x d ∈ vals := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt, Option.getD_some]
  exact List.getElem_mem lt

theorem fill_bounded {n : ℕ} {vals : List Tm} (bounded : ∀ t ∈ vals, Bounded n t) :
    ∀ p : Pat, Bounded n (Pat.fill vals p)
  | .var x => by
      by_cases lt : x < vals.length
      · exact bounded _ (getD_mem lt _)
      · show Bounded n (vals.getD x (.const 0))
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
        intro v hv
        simp [Term.freeVars] at hv
  | .sym _ => fun v hv => by simp [Pat.fill, Term.freeVars] at hv
  | .cell a b => fun v hv => by
      rcases mem_freeVars_node.mp hv with hv | hv
      · exact fill_bounded bounded a v hv
      · exact fill_bounded bounded b v hv

theorem fill_vars_sub {vals : List Tm} : ∀ (p : Pat) {x : ℕ}, x ∈ p.vars →
    (vals.getD x (.const 0)).freeVars ⊆ (Pat.fill vals p).freeVars
  | .var y, x, hx => by
      simp only [Pat.vars, List.mem_singleton] at hx
      subst hx
      exact subset_rfl
  | .sym _, _, hx => by simp [Pat.vars] at hx
  | .cell a b, x, hx => by
      simp only [Pat.vars, List.mem_append] at hx
      intro v hv
      rw [Pat.fill, mem_freeVars_node]
      rcases hx with hx | hx
      · exact .inl (fill_vars_sub a hx hv)
      · exact .inr (fill_vars_sub b hx hv)

/-- Every value of a covered pattern occurs in its instance, so it is as bounded as the instance. -/
theorem vals_bounded_of_fill {n : ℕ} {vals : List Tm} {p : Pat} (bounded : Bounded n (Pat.fill vals p))
    (covers : ∀ x < vals.length, x ∈ p.vars) : ∀ t ∈ vals, Bounded n t := by
  intro t member v hv
  obtain ⟨i, lt, rfl⟩ := List.getElem_of_mem member
  have same : vals.getD i (.const 0) = vals[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt, Option.getD_some]
  exact bounded v (fill_vars_sub p (covers i lt) (same ▸ hv))

theorem mem_at_freeVars (n : ℕ) : ∀ (p : Pat) {x : ℕ}, x ∈ p.vars → (n, x) ∈ (p.at n).freeVars
  | .var y, x, hx => by
      simp only [Pat.vars, List.mem_singleton] at hx
      subst hx
      rw [Pat.at, Term.mem_freeVars_var (σ := rows)]
  | .sym _, _, hx => by simp [Pat.vars] at hx
  | .cell a b, x, hx => by
      simp only [Pat.vars, List.mem_append] at hx
      rw [Pat.at, mem_freeVars_node]
      rcases hx with hx | hx
      · exact .inl (mem_at_freeVars n a hx)
      · exact .inr (mem_at_freeVars n b hx)

/-! ## The matcher -/

/-- **The matcher at scope `n`**: the `x`-th variable of the scope goes to the `x`-th value. -/
def matcher (n : ℕ) (vals : List Tm) : Subst rows := fun v =>
  if v.1 = n ∧ v.2 < vals.length then vals.getD v.2 (.const 0) else .var v

theorem matcher_at {n : ℕ} {vals : List Tm} : ∀ (p : Pat), (∀ x ∈ p.vars, x < vals.length) →
    (matcher n vals).applyTerm (p.at n) = Pat.fill vals p
  | .var x, within => by
      have lt := within x (by simp [Pat.vars])
      show matcher n vals (n, x) = vals.getD x (.const 0)
      rw [matcher, if_pos ⟨rfl, lt⟩]
  | .sym _, _ => rfl
  | .cell a b, within => by
      rw [Pat.at, apply_node, matcher_at a fun x hx => within x (by simp [Pat.vars, hx]),
        matcher_at b fun x hx => within x (by simp [Pat.vars, hx])]
      rfl

/-- **The matcher fixes every term below its scope.** -/
theorem matcher_fixes {n : ℕ} {vals : List Tm} {t : Tm} (bounded : Bounded n t) :
    (matcher n vals).applyTerm t = t :=
  Subst.applyTerm_eq_self fun v hv => by
    have lt := bounded v hv
    rw [matcher, if_neg fun h => absurd h.1 (by omega)]

theorem unifies_single_iff (δ : Subst rows) (s t : Tm) :
    Unifies δ [(s, t)] ↔ δ.applyTerm s = δ.applyTerm t := by
  simp [Unifies]

theorem agree_fill {δ : Subst rows} {n : ℕ} {vals : List Tm} : ∀ (p : Pat),
    δ.applyTerm (p.at n) = δ.applyTerm (Pat.fill vals p) →
      ∀ x ∈ p.vars, δ (n, x) = δ.applyTerm (vals.getD x (.const 0))
  | .var y, same, x, hx => by
      simp only [Pat.vars, List.mem_singleton] at hx
      subst hx
      exact same
  | .sym _, _, _, hx => by simp [Pat.vars] at hx
  | .cell a b, same, x, hx => by
      rw [Pat.at, Pat.fill, apply_node, apply_node, node_inj] at same
      simp only [Pat.vars, List.mem_append] at hx
      rcases hx with hx | hx
      · exact agree_fill a same.1 x hx
      · exact agree_fill b same.2 x hx

/-- **The matcher is a most general unifier** of a pattern at a fresh scope with its instance. -/
theorem matcher_isMGU {n : ℕ} {vals : List Tm} (bounded : ∀ t ∈ vals, Bounded n t) {p : Pat}
    (covers : ∀ x < vals.length, x ∈ p.vars) (within : ∀ x ∈ p.vars, x < vals.length) :
    IsMGU [(p.at n, Pat.fill vals p)] (matcher n vals) := by
  have filled : Bounded n (Pat.fill vals p) := fill_bounded bounded p
  refine ⟨?_, ?_, ?_⟩
  · rw [unifies_single_iff, matcher_at p within, matcher_fixes filled]
  · intro δ unifies
    rw [unifies_single_iff] at unifies
    have agree := agree_fill p unifies
    refine ⟨δ, fun v => ?_⟩
    by_cases moved : v.1 = n ∧ v.2 < vals.length
    · rw [matcher, if_pos moved]
      have hv : v = (n, v.2) := Prod.ext moved.1 rfl
      rw [hv]
      exact agree v.2 (covers v.2 moved.2)
    · rw [matcher, if_neg moved, Subst.applyTerm_var]
  · have inX : ∀ {w : ℕ × ℕ}, w ∈ (p.at n).freeVars ∨ w ∈ (Pat.fill vals p).freeVars →
        w ∈ eqVars [(p.at n, Pat.fill vals p)] := fun h => by
      simp only [eqVars, Finset.union_empty, Finset.mem_union]
      exact h
    refine ⟨fun v notIn => ?_, fun v _ => ?_, fun v w hw => ?_⟩
    · by_cases moved : v.1 = n ∧ v.2 < vals.length
      · have hv : v = (n, v.2) := Prod.ext moved.1 rfl
        exact absurd (inX (.inl (hv ▸ mem_at_freeVars n p (covers v.2 moved.2)))) notIn
      · rw [matcher, if_neg moved]
    · by_cases moved : v.1 = n ∧ v.2 < vals.length
      · rw [matcher, if_pos moved]
        exact fun w hw => inX (.inr (fill_vars_sub p (covers v.2 moved.2) hw))
      · rw [matcher, if_neg moved]
        intro w hw
        rw [Term.mem_freeVars_var (σ := rows)] at hw
        subst hw
        assumption
    · by_cases moved : v.1 = n ∧ v.2 < vals.length
      · rw [matcher, if_pos moved] at hw
        have lt := bounded _ (getD_mem moved.2 _) w hw
        rw [matcher, if_neg fun h => absurd h.1 (by omega)]
      · rw [matcher, if_neg moved, Term.mem_freeVars_var (σ := rows)] at hw
        subst hw
        rw [matcher, if_neg moved]

/-! ## Extension by a fresh variable, and equal sides -/

/-- `θ` with the variable `v` bound to the image of `K`. -/
def extendAt (θ : Subst rows) (v : ℕ × ℕ) (K : Tm) : Subst rows := fun x =>
  if x = v then θ.applyTerm K else θ x

theorem extendAt_agree {θ : Subst rows} {v : ℕ × ℕ} {K t : Tm} (fresh : v ∉ t.freeVars) :
    (extendAt θ v K).applyTerm t = θ.applyTerm t :=
  Subst.applyTerm_congr fun x hx => by
    rw [extendAt, if_neg fun h : x = v => fresh (by rw [← h]; exact hx)]

/-- **Extension by a fresh variable keeps a most general unifier most general.** -/
theorem isMGU_extend {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) {v : ℕ × ℕ} {K : Tm}
    (freshP : v ∉ eqVars P) (freshK : v ∉ K.freeVars) :
    IsMGU ((.var v, K) :: P) (extendAt θ v K) := by
  have agreeP : ∀ e ∈ P, ∀ x ∈ e.1.freeVars ∪ e.2.freeVars, x ≠ v := by
    intro e member x hx same
    subst same
    exact freshP ((mem_eqVars (σ := rows)).mpr ⟨e, member, Finset.mem_union.mp hx⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    rcases List.mem_cons.mp member with rfl | member
    · show extendAt θ v K v = (extendAt θ v K).applyTerm K
      rw [extendAt, if_pos rfl, extendAt_agree freshK]
    · rw [extendAt_agree fun h => agreeP e member v (Finset.mem_union_left _ h) rfl,
        extendAt_agree fun h => agreeP e member v (Finset.mem_union_right _ h) rfl]
      exact mgu.unifies e member
  · intro δ unifies
    obtain ⟨ρ, factor⟩ := mgu.general δ fun e member => unifies e (List.mem_cons_of_mem _ member)
    refine ⟨ρ, fun x => ?_⟩
    by_cases same : x = v
    · subst same
      have pair := unifies (.var x, K) List.mem_cons_self
      rw [Subst.applyTerm_var] at pair
      rw [pair, extendAt, if_pos rfl, ← Subst.applyTerm_comp]
      exact Subst.applyTerm_congr fun y _ => factor y
    · rw [extendAt, if_neg same]
      exact factor x
  · have vars : eqVars ((.var v, K) :: P) = ({v} ∪ K.freeVars) ∪ eqVars P := by
      simp [eqVars, Term.freeVars]
    rw [vars]
    have range_sub : ∀ t : Tm, (θ.applyTerm t).freeVars ⊆ t.freeVars ∪ eqVars P :=
      mgu.relevant.freeVars_applyTerm_subset
    refine ⟨fun x notIn => ?_, fun x xIn => ?_, fun x w hw => ?_⟩
    · have ne : x ≠ v := fun h => notIn (by simp [h])
      rw [extendAt, if_neg ne]
      exact mgu.relevant.fixes x fun h => notIn (Finset.mem_union_right _ h)
    · by_cases same : x = v
      · rw [extendAt, if_pos same]
        intro w hw
        rcases Finset.mem_union.mp (range_sub K hw) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ h
      · rw [extendAt, if_neg same]
        intro w hw
        rcases em (x ∈ eqVars P) with inP | inP
        · exact Finset.mem_union_right _ (mgu.relevant.range x inP hw)
        · rw [mgu.relevant.fixes x inP, Term.mem_freeVars_var (σ := rows)] at hw
          subst hw
          exact xIn
    · have notV : ∀ t : Tm, v ∉ t.freeVars → w ∈ (θ.applyTerm t).freeVars → w ≠ v := by
        intro t fresh member same
        subst same
        rcases Finset.mem_union.mp (range_sub t member) with h | h
        · exact fresh h
        · exact freshP h
      by_cases same : x = v
      · rw [extendAt, if_pos same] at hw
        rw [extendAt, if_neg (notV K freshK hw)]
        obtain ⟨y, -, hy⟩ := (Subst.mem_freeVars_applyTerm (σ := rows)).mp hw
        exact mgu.relevant.unbound y w hy
      · rw [extendAt, if_neg same] at hw
        have wne : w ≠ v := by
          rcases em (x ∈ eqVars P) with inP | inP
          · intro h
            subst h
            exact freshP (mgu.relevant.range x inP hw)
          · rw [mgu.relevant.fixes x inP, Term.mem_freeVars_var (σ := rows)] at hw
            rw [hw]
            exact same
        rw [extendAt, if_neg wne]
        exact mgu.relevant.unbound x w hw

/-- **A problem whose sides are equal has the identity as most general unifier.** -/
theorem isMGU_id_of_eq {P : List (Tm × Tm)} (equal : ∀ e ∈ P, e.1 = e.2) : IsMGU P (Subst.id rows) :=
  ⟨fun e member => by rw [equal e member], fun δ _ => Subst.id_moreGeneral δ,
    Subst.relevantIdempotent_id _⟩

#print axioms getD_mem
#print axioms fill_bounded
#print axioms vals_bounded_of_fill
#print axioms matcher_at
#print axioms matcher_fixes
#print axioms matcher_isMGU
#print axioms isMGU_extend
#print axioms isMGU_id_of_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
