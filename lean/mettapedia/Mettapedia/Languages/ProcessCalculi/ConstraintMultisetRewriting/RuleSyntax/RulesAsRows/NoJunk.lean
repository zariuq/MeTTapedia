import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Interpreter

/-!
# The code algebra has no junk solutions over drop-free terms

The code algebra `Expr` adds `drop` to plain first-order terms (unknowns, symbols, binary cells and the
constants `slot n i`), and reads equations modulo normal forms. Its solutions may send unknowns to
stuck drops, terms that are not first-order. A store of drop-free equations does not become solvable,
and no property of drop-free terms changes, because of those extra values.

**Squashing** (`squash K`) replaces every `drop c e` by the cell `cell (sym K) (cell c e)`
(recursively), with `K` a symbol above every symbol in sight. It commutes with substitution on
drop-free terms (`squash_subst`) and is injective on terms whose symbols lie below `K`
(`squash_injective`). So every solution in the code algebra gives a drop-free solution that equates
exactly the same pairs among any finite list of drop-free terms (`squash_solution`); drop-free
solutions are read syntactically (`nf_subst_of_dropFree`). Consequences:

* `consistent_iff_firstOrder`: a store of drop-free equations is consistent in the code algebra
  exactly when it has a first-order (drop-free, syntactic) solution;
* `forall_iff_firstOrder`: any property of the equality pattern of finitely many drop-free terms holds
  at every solution in the code algebra exactly when it holds at every first-order solution. Equation
  guards, absence and count checks and census sets at a solution are such properties (of the pattern
  among the checks' terms and the rows).

Controls: a stuck value of the code algebra that is not first-order (`stuck_value_squashes`); squashing
with its symbol among the term's symbols identifies a drop and a cell (`squash_needs_bound`); distinct
stuck values stay apart (`squash_keeps_apart`).

Not compared here: the freshness of openings, so the step over `Expr` as a whole is not compared with
a first-order step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.NoJunk

open Expr

/-! ## Symbols and squashing -/

/-- One more than the largest symbol of a term (zero when it has none). -/
def symBound : Expr → ℕ
  | .var _ => 0
  | .sym k => k + 1
  | .cell a b => max (symBound a) (symBound b)
  | .slot _ _ => 0
  | .drop c e => max (symBound c) (symBound e)

/-- **Squashing**: every `drop c e` becomes `cell (sym K) (cell c e)`, recursively. -/
def squash (K : ℕ) : Expr → Expr
  | .var v => .var v
  | .sym k => .sym k
  | .cell a b => .cell (squash K a) (squash K b)
  | .slot n i => .slot n i
  | .drop c e => .cell (.sym K) (.cell (squash K c) (squash K e))

theorem squash_dropFree (K : ℕ) : ∀ t : Expr, (squash K t).dropFree = true
  | .var _ => rfl
  | .sym _ => rfl
  | .cell a b => by
      simp only [squash, dropFree, Bool.and_eq_true]
      exact ⟨squash_dropFree K a, squash_dropFree K b⟩
  | .slot _ _ => rfl
  | .drop c e => by
      simp [squash, dropFree, squash_dropFree K c, squash_dropFree K e]

/-- **Squashing commutes with substitution on drop-free terms.** -/
theorem squash_subst (K : ℕ) (τ : ℕ → Expr) : ∀ {t : Expr}, t.dropFree = true →
    squash K (subst τ t) = subst (fun v => squash K (τ v)) t
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [subst, squash]
      rw [squash_subst K τ free.1, squash_subst K τ free.2]
  | .slot _ _, _ => rfl
  | .drop _ _, free => by simp [dropFree] at free

/-- A squashed term is a symbol only when the term is that symbol. -/
theorem eq_sym_of_squash {K j : ℕ} : ∀ {x : Expr}, squash K x = .sym j → x = .sym j
  | .var _, same => by simp [squash] at same
  | .sym _, same => by simpa [squash] using same
  | .cell _ _, same => by simp [squash] at same
  | .slot _ _, same => by simp [squash] at same
  | .drop _ _, same => by simp [squash] at same

/-- **Squashing is injective below its symbol.** -/
theorem squash_injective (K : ℕ) : ∀ {a b : Expr}, symBound a ≤ K → symBound b ≤ K →
    squash K a = squash K b → a = b
  | .var _, .var _, _, _, same => by simpa [squash] using same
  | .sym _, .sym _, _, _, same => by simpa [squash] using same
  | .slot _ _, .slot _ _, _, _, same => by simpa [squash] using same
  | .cell x y, .cell x' y', ha, hb, same => by
      simp only [squash, Expr.cell.injEq] at same
      simp only [symBound, max_le_iff] at ha hb
      rw [squash_injective K ha.1 hb.1 same.1, squash_injective K ha.2 hb.2 same.2]
  | .drop c e, .drop c' e', ha, hb, same => by
      simp only [squash, Expr.cell.injEq, true_and] at same
      simp only [symBound, max_le_iff] at ha hb
      rw [squash_injective K ha.1 hb.1 same.1, squash_injective K ha.2 hb.2 same.2]
  | .cell x _, .drop _ _, ha, _, same => by
      simp only [squash, Expr.cell.injEq] at same
      have isK := eq_sym_of_squash same.1
      subst isK
      simp [symBound] at ha
  | .drop _ _, .cell x _, _, hb, same => by
      simp only [squash, Expr.cell.injEq] at same
      have isK := eq_sym_of_squash same.1.symm
      subst isK
      simp [symBound] at hb
  | .var _, .sym _, _, _, same => by simp [squash] at same
  | .var _, .cell _ _, _, _, same => by simp [squash] at same
  | .var _, .slot _ _, _, _, same => by simp [squash] at same
  | .var _, .drop _ _, _, _, same => by simp [squash] at same
  | .sym _, .var _, _, _, same => by simp [squash] at same
  | .sym _, .cell _ _, _, _, same => by simp [squash] at same
  | .sym _, .slot _ _, _, _, same => by simp [squash] at same
  | .sym _, .drop _ _, _, _, same => by simp [squash] at same
  | .cell _ _, .var _, _, _, same => by simp [squash] at same
  | .cell _ _, .sym _, _, _, same => by simp [squash] at same
  | .cell _ _, .slot _ _, _, _, same => by simp [squash] at same
  | .slot _ _, .var _, _, _, same => by simp [squash] at same
  | .slot _ _, .sym _, _, _, same => by simp [squash] at same
  | .slot _ _, .cell _ _, _, _, same => by simp [squash] at same
  | .slot _ _, .drop _ _, _, _, same => by simp [squash] at same
  | .drop _ _, .var _, _, _, same => by simp [squash] at same
  | .drop _ _, .sym _, _, _, same => by simp [squash] at same
  | .drop _ _, .slot _ _, _, _, same => by simp [squash] at same

/-! ## Drop-free terms are read syntactically -/

theorem dropFree_subst {σ : ℕ → Expr} (vals : ∀ v, (σ v).dropFree = true) :
    ∀ {t : Expr}, t.dropFree = true → (subst σ t).dropFree = true
  | .var v, _ => vals v
  | .sym _, _ => rfl
  | .cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [subst, dropFree, Bool.and_eq_true]
      exact ⟨dropFree_subst vals free.1, dropFree_subst vals free.2⟩
  | .slot _ _, _ => rfl
  | .drop _ _, free => by simp [dropFree] at free

theorem nf_of_dropFree : ∀ {t : Expr}, t.dropFree = true → nf t = t
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [nf]
      rw [nf_of_dropFree free.1, nf_of_dropFree free.2]
  | .slot _ _, _ => rfl
  | .drop _ _, free => by simp [dropFree] at free

/-- **Drop-free solutions are read syntactically.** -/
theorem nf_subst_of_dropFree {σ : ℕ → Expr} (vals : ∀ v, (σ v).dropFree = true) {t : Expr}
    (free : t.dropFree = true) : nf (subst σ t) = subst σ t :=
  nf_of_dropFree (dropFree_subst vals free)

/-! ## Squashing a solution -/

/-- **No junk**: for every solution `σ` of the code algebra and every finite list of drop-free terms,
there is a drop-free solution `σ'` that equates, syntactically, exactly the pairs of the list that `σ`
equates modulo normal forms. -/
theorem squash_solution (T : List Expr) (free : ∀ a ∈ T, a.dropFree = true) (σ : ℕ → Expr) :
    ∃ σ' : ℕ → Expr, (∀ v, (σ' v).dropFree = true) ∧
      ∀ a ∈ T, ∀ b ∈ T, (nf (subst σ a) = nf (subst σ b) ↔ subst σ' a = subst σ' b) := by
  let K := maxOf (T.map fun a => symBound (nf (subst σ a)))
  have below : ∀ a ∈ T, symBound (nf (subst σ a)) ≤ K := fun a inside =>
    le_maxOf (List.mem_map.mpr ⟨a, inside, rfl⟩)
  refine ⟨fun v => squash K (nf (σ v)), fun v => squash_dropFree K _, fun a ha b hb => ?_⟩
  have read : ∀ c ∈ T, subst (fun v => squash K (nf (σ v))) c = squash K (nf (subst σ c)) := by
    intro c hc
    rw [nf_subst_dropFree σ (free c hc), squash_subst K _ (free c hc)]
  rw [read a ha, read b hb]
  exact ⟨fun same => by rw [same], squash_injective K (below a ha) (below b hb)⟩

/-! ## Consequences -/

/-- **Conservativity of consistency**: a store of drop-free equations is consistent in the code algebra
exactly when it has a first-order solution (drop-free values, syntactic equality). -/
theorem consistent_iff_firstOrder (store : EquationStore Expr)
    (free : ∀ e ∈ store, e.1.dropFree = true ∧ e.2.dropFree = true) :
    action.Consistent store ↔
      ∃ σ' : ℕ → Expr, (∀ v, (σ' v).dropFree = true) ∧ ∀ e ∈ store, subst σ' e.1 = subst σ' e.2 := by
  constructor
  · rintro ⟨σ, solved⟩
    let T := store.map Prod.fst ++ store.map Prod.snd
    have freeT : ∀ a ∈ T, a.dropFree = true := by
      intro a inside
      rcases List.mem_append.mp inside with left | right
      · obtain ⟨e, member, rfl⟩ := List.mem_map.mp left
        exact (free e member).1
      · obtain ⟨e, member, rfl⟩ := List.mem_map.mp right
        exact (free e member).2
    obtain ⟨σ', vals, same⟩ := squash_solution T freeT σ
    refine ⟨σ', vals, fun e member => ?_⟩
    exact (same e.1 (List.mem_append_left _ (List.mem_map_of_mem member))
      e.2 (List.mem_append_right _ (List.mem_map_of_mem member))).mp (solved e member)
  · rintro ⟨σ', vals, solved⟩
    refine ⟨σ', fun e member => ?_⟩
    show nf (subst σ' e.1) = nf (subst σ' e.2)
    rw [nf_subst_of_dropFree vals (free e member).1, nf_subst_of_dropFree vals (free e member).2]
    exact solved e member

/-- **Conservativity of every property of an equality pattern**: for drop-free equations and a finite
list `T` of drop-free terms containing their sides, a property of which pairs of `T` are equal holds at
every solution of the code algebra exactly when it holds at every first-order solution. -/
theorem forall_iff_firstOrder (T : List Expr) (free : ∀ a ∈ T, a.dropFree = true)
    (store : EquationStore Expr) (sides : ∀ e ∈ store, e.1 ∈ T ∧ e.2 ∈ T)
    (Φ : (Expr → Expr → Prop) → Prop)
    (pattern : ∀ R R' : Expr → Expr → Prop, (∀ a ∈ T, ∀ b ∈ T, (R a b ↔ R' a b)) → (Φ R ↔ Φ R')) :
    (∀ σ : ℕ → Expr, action.Models σ store → Φ fun a b => nf (subst σ a) = nf (subst σ b)) ↔
      ∀ σ' : ℕ → Expr, (∀ v, (σ' v).dropFree = true) → (∀ e ∈ store, subst σ' e.1 = subst σ' e.2) →
        Φ fun a b => subst σ' a = subst σ' b := by
  constructor
  · intro all σ' vals solved
    have models : action.Models σ' store := by
      intro e member
      show nf (subst σ' e.1) = nf (subst σ' e.2)
      rw [nf_subst_of_dropFree vals (free _ (sides e member).1),
        nf_subst_of_dropFree vals (free _ (sides e member).2)]
      exact solved e member
    have equiv := pattern (fun a b => nf (subst σ' a) = nf (subst σ' b))
      (fun a b => subst σ' a = subst σ' b) (fun a ha b hb => by
        show nf (subst σ' a) = nf (subst σ' b) ↔ subst σ' a = subst σ' b
        rw [nf_subst_of_dropFree vals (free a ha), nf_subst_of_dropFree vals (free b hb)])
    exact equiv.mp (all σ' models)
  · intro all σ models
    obtain ⟨σ', vals, same⟩ := squash_solution T free σ
    have solved : ∀ e ∈ store, subst σ' e.1 = subst σ' e.2 := fun e member =>
      (same e.1 (sides e member).1 e.2 (sides e member).2).mp (models e member)
    have equiv := pattern (fun a b => nf (subst σ a) = nf (subst σ b))
      (fun a b => subst σ' a = subst σ' b) (fun a ha b hb => same a ha b hb)
    exact equiv.mpr (all σ' vals solved)

/-! ## Controls -/

/-- **A value of the code algebra that is not first-order**: the drop of an unknown at an unknown is
its own normal form; squashing turns it into a drop-free cell. -/
theorem stuck_value_squashes :
    nf (Expr.drop (.var 1) (.var 2)) = .drop (.var 1) (.var 2) ∧
      (squash 3 (.drop (.var 1) (.var 2))).dropFree = true :=
  ⟨rfl, rfl⟩

/-- **Squashing below its symbol is needed**: with `K` among the symbols, a drop and a cell squash
alike. -/
theorem squash_needs_bound :
    squash 0 (.drop (.var 1) (.var 2)) = squash 0 (.cell (.sym 0) (.cell (.var 1) (.var 2))) ∧
      (Expr.drop (.var 1) (.var 2)) ≠ .cell (.sym 0) (.cell (.var 1) (.var 2)) :=
  ⟨rfl, by simp⟩

/-- **Distinct stuck values stay apart**: two different normal stuck drops squash to different
first-order terms. -/
theorem squash_keeps_apart :
    squash 9 (.drop (.var 1) (.var 2)) ≠ squash 9 (.drop (.var 2) (.var 1)) := by
  simp [squash]

#print axioms squash_injective
#print axioms squash_solution
#print axioms nf_subst_of_dropFree
#print axioms consistent_iff_firstOrder
#print axioms forall_iff_firstOrder
#print axioms stuck_value_squashes
#print axioms squash_needs_bound
#print axioms squash_keeps_apart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.NoJunk
