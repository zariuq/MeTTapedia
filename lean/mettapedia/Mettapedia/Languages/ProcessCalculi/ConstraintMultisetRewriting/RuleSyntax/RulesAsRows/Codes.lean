import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# Codes as terms: closed codes, levelled slots, and instantiation at an environment

A term theory in which a rule can be stored as a row and opened by matching.

* **Terms** (`Expr`): unknowns `var v`, symbols `sym k`, binary cells `cell a b`, slots `slot n i`
  (the `i`-th unknown of a code, at quotation level `n`), and `drop c e`: the code `c` instantiated at
  the environment `e`.
* **Closed codes** (`closed`): terms built from symbols, cells and slots. Substitution fixes them.
* **Quotation** (`quote`): a drop-free term becomes a closed code; an unknown `v` becomes the slot
  `slot 0 v`, a slot moves up one level. It is a bijection between drop-free terms and closed codes
  (`unquote_quote`, `quote_unquote`).
* **The declared equality** is equality of normal forms (`nf`): a `drop` of a closed code fills its
  level-0 slots from the environment, a list of cells (`pick`), and lowers the other slots by one level
  (`fill`); a `drop` of anything else waits. Everything else is free syntax.

The laws that make this a substitution action (`action`): substitution commutes with normal forms
(`nf_subst_nf`), so equal normal forms stay equal under every substitution. The law that makes a
code openable by one unknown: **dropping the quotation of a term at an environment instantiates the
term's unknowns by the environment's entries** (`nf_drop_quote`). One unknown standing for an
environment therefore opens any number of a code's unknowns, at any depth.

Environments and the lists inside codes are cell lists ending in `nil` (`lst`); `pick_lst` reads them.
Rows are tagged: `obj t` for data, `code c` for a stored rule; the tags never meet (`obj_ne_code`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows

/-- **Terms with codes.** -/
inductive Expr where
  | var (v : ℕ)
  | sym (k : ℕ)
  | cell (head tail : Expr)
  | slot (level index : ℕ)
  | drop (code env : Expr)
  deriving DecidableEq

namespace Expr

/-! ## Substitution of unknowns -/

/-- Substitute the unknowns. -/
def subst (σ : ℕ → Expr) : Expr → Expr
  | var v => σ v
  | sym k => sym k
  | cell a b => cell (subst σ a) (subst σ b)
  | slot n i => slot n i
  | drop c e => drop (subst σ c) (subst σ e)

theorem subst_var : ∀ t : Expr, subst var t = t
  | var _ => rfl
  | sym _ => rfl
  | cell a b => by simp only [subst]; rw [subst_var a, subst_var b]
  | slot _ _ => rfl
  | drop c e => by simp only [subst]; rw [subst_var c, subst_var e]

theorem subst_subst (σ τ : ℕ → Expr) : ∀ t : Expr,
    subst σ (subst τ t) = subst (fun v => subst σ (τ v)) t
  | var _ => rfl
  | sym _ => rfl
  | cell a b => by simp only [subst]; rw [subst_subst σ τ a, subst_subst σ τ b]
  | slot _ _ => rfl
  | drop c e => by simp only [subst]; rw [subst_subst σ τ c, subst_subst σ τ e]

/-- One more than the largest unknown of a term (zero when it has none). -/
def bound : Expr → ℕ
  | var v => v + 1
  | sym _ => 0
  | cell a b => max (bound a) (bound b)
  | slot _ _ => 0
  | drop c e => max (bound c) (bound e)

/-- **Substitution depends only on the unknowns below the bound.** -/
theorem subst_congr {σ τ : ℕ → Expr} : ∀ t : Expr, (∀ v, v < bound t → σ v = τ v) →
    subst σ t = subst τ t
  | var v, same => same v (Nat.lt_succ_self v)
  | sym _, _ => rfl
  | cell a b, same => by
      simp only [subst]
      rw [subst_congr a fun v lt => same v (lt_of_lt_of_le lt (le_max_left _ _)),
        subst_congr b fun v lt => same v (lt_of_lt_of_le lt (le_max_right _ _))]
  | slot _ _, _ => rfl
  | drop c e, same => by
      simp only [subst]
      rw [subst_congr c fun v lt => same v (lt_of_lt_of_le lt (le_max_left _ _)),
        subst_congr e fun v lt => same v (lt_of_lt_of_le lt (le_max_right _ _))]

/-! ## Closed codes, environments and normal forms -/

/-- **Closed codes**: symbols, cells and slots. -/
def closed : Expr → Bool
  | sym _ => true
  | slot _ _ => true
  | cell a b => closed a && closed b
  | _ => false

/-- **The `i`-th entry of an environment**, a list of cells; it waits when the environment is not a
cell. -/
def pick : ℕ → Expr → Expr
  | 0, cell a _ => a
  | i + 1, cell _ rest => pick i rest
  | i, e => drop (slot 0 i) e

/-- **Fill a closed code** from an environment: level-0 slots are read from it, other slots go down
one level. -/
def fill (e : Expr) : Expr → Expr
  | slot 0 i => pick i e
  | slot (n + 1) i => slot n i
  | cell a b => cell (fill e a) (fill e b)
  | t => t

/-- Instantiate a code at an environment: fill it when it is closed, wait otherwise. -/
def inst (c e : Expr) : Expr := if c.closed then fill e c else drop c e

/-- **Normal forms.** -/
def nf : Expr → Expr
  | var v => var v
  | sym k => sym k
  | cell a b => cell (nf a) (nf b)
  | slot n i => slot n i
  | drop c e => inst (nf c) (nf e)

theorem subst_of_closed (σ : ℕ → Expr) : ∀ {c : Expr}, c.closed → subst σ c = c
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, closedAB => by
      simp only [closed, Bool.and_eq_true] at closedAB
      simp only [subst]
      rw [subst_of_closed σ closedAB.1, subst_of_closed σ closedAB.2]
  | var _, closedV => by simp [closed] at closedV
  | drop _ _, closedD => by simp [closed] at closedD

theorem nf_of_closed : ∀ {c : Expr}, c.closed → nf c = c
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, closedAB => by
      simp only [closed, Bool.and_eq_true] at closedAB
      simp only [nf]
      rw [nf_of_closed closedAB.1, nf_of_closed closedAB.2]
  | var _, closedV => by simp [closed] at closedV
  | drop _ _, closedD => by simp [closed] at closedD

theorem pick_of_not_cell {e : Expr} (notCell : ∀ a b, e ≠ cell a b) (i : ℕ) :
    pick i e = drop (slot 0 i) e := by
  cases e with
  | cell a b => exact absurd rfl (notCell a b)
  | var _ => cases i <;> rfl
  | sym _ => cases i <;> rfl
  | slot _ _ => cases i <;> rfl
  | drop _ _ => cases i <;> rfl

@[simp] theorem pick_cell_zero (a rest : Expr) : pick 0 (cell a rest) = a := rfl

@[simp] theorem pick_cell_succ (i : ℕ) (a rest : Expr) : pick (i + 1) (cell a rest) = pick i rest := rfl

/-- A dropped level-0 slot picks from the environment. -/
theorem nf_drop_slot (i : ℕ) (e : Expr) : nf (drop (slot 0 i) e) = pick i (nf e) := by
  simp [nf, inst, closed, fill]

theorem nf_subst_pick (σ : ℕ → Expr) : ∀ (e : Expr) (i : ℕ),
    nf (subst σ (pick i e)) = pick i (nf (subst σ e))
  | cell a rest, 0 => by simp [subst, nf]
  | cell a rest, i + 1 => by
      simp only [pick_cell_succ, subst, nf]
      exact nf_subst_pick σ rest i
  | var v, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
      simp only [subst, nf_drop_slot]
  | sym k, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
      simp only [subst, nf_drop_slot]
  | slot n j, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
      simp only [subst, nf_drop_slot]
  | drop c e, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
      simp only [subst, nf_drop_slot]

theorem nf_subst_fill (σ : ℕ → Expr) (e : Expr) : ∀ {c : Expr}, c.closed →
    nf (subst σ (fill e c)) = fill (nf (subst σ e)) c
  | slot 0 i, _ => nf_subst_pick σ e i
  | slot (n + 1) i, _ => rfl
  | sym _, _ => rfl
  | cell a b, closedAB => by
      simp only [closed, Bool.and_eq_true] at closedAB
      simp only [fill, subst, nf]
      rw [nf_subst_fill σ e closedAB.1, nf_subst_fill σ e closedAB.2]
  | var _, closedV => by simp [closed] at closedV
  | drop _ _, closedD => by simp [closed] at closedD

theorem nf_subst_inst (σ : ℕ → Expr) (c e : Expr) :
    nf (subst σ (inst c e)) = inst (nf (subst σ c)) (nf (subst σ e)) := by
  by_cases closedC : c.closed
  · rw [inst, if_pos closedC, nf_subst_fill σ e closedC, subst_of_closed σ closedC,
      nf_of_closed closedC, inst, if_pos closedC]
  · rw [inst, if_neg closedC]
    rfl

/-- **Substitution commutes with normal forms.** -/
theorem nf_subst_nf (σ : ℕ → Expr) : ∀ t : Expr, nf (subst σ (nf t)) = nf (subst σ t)
  | var _ => rfl
  | sym _ => rfl
  | cell a b => by
      simp only [nf, subst]
      rw [nf_subst_nf σ a, nf_subst_nf σ b]
  | slot _ _ => rfl
  | drop c e => by
      simp only [nf]
      rw [nf_subst_inst, nf_subst_nf σ c, nf_subst_nf σ e]
      rfl

theorem nf_nf (t : Expr) : nf (nf t) = nf t := by
  have same := nf_subst_nf var t
  rwa [subst_var, subst_var] at same

/-! ## The substitution action -/

/-- **The code algebra as a substitution action**: equality of normal forms, substitution of unknowns. -/
def action : SubstitutionAction Expr (ℕ → Expr) where
  E s t := nf s = nf t
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun one two => one.trans two⟩
  apply := subst
  identity := var
  compose σ τ v := subst σ (τ v)
  apply_identity := subst_var
  apply_compose σ τ t := (subst_subst σ τ t).symm
  preserves σ {s t} same := by
    show nf (subst σ s) = nf (subst σ t)
    have same' : nf s = nf t := same
    rw [← nf_subst_nf σ s, ← nf_subst_nf σ t, same']

theorem action_E (s t : Expr) : action.E s t ↔ nf s = nf t := Iff.rfl

/-! ## Quotation -/

/-- Terms without `drop`. -/
def dropFree : Expr → Bool
  | drop _ _ => false
  | cell a b => dropFree a && dropFree b
  | _ => true

/-- **Quotation**: unknowns become level-0 slots, slots move up a level. -/
def quote : Expr → Expr
  | var v => slot 0 v
  | sym k => sym k
  | cell a b => cell (quote a) (quote b)
  | slot n i => slot (n + 1) i
  | drop c e => drop (quote c) (quote e)

/-- **Unquotation** of a closed code. -/
def unquote : Expr → Expr
  | slot 0 v => var v
  | slot (n + 1) i => slot n i
  | cell a b => cell (unquote a) (unquote b)
  | t => t

theorem quote_closed : ∀ {t : Expr}, t.dropFree → (quote t).closed
  | var _, _ => rfl
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp [quote, closed, quote_closed free.1, quote_closed free.2]
  | drop _ _, free => by simp [dropFree] at free

theorem unquote_quote : ∀ {t : Expr}, t.dropFree → unquote (quote t) = t
  | var _, _ => rfl
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [quote, unquote]
      rw [unquote_quote free.1, unquote_quote free.2]
  | drop _ _, free => by simp [dropFree] at free

theorem quote_unquote : ∀ {c : Expr}, c.closed → quote (unquote c) = c
  | slot 0 _, _ => rfl
  | slot (_ + 1) _, _ => rfl
  | sym _, _ => rfl
  | cell a b, closedAB => by
      simp only [closed, Bool.and_eq_true] at closedAB
      simp only [unquote, quote]
      rw [quote_unquote closedAB.1, quote_unquote closedAB.2]
  | var _, closedV => by simp [closed] at closedV
  | drop _ _, closedD => by simp [closed] at closedD

theorem unquote_dropFree : ∀ {c : Expr}, c.closed → (unquote c).dropFree
  | slot 0 _, _ => rfl
  | slot (_ + 1) _, _ => rfl
  | sym _, _ => rfl
  | cell a b, closedAB => by
      simp only [closed, Bool.and_eq_true] at closedAB
      simp [unquote, dropFree, unquote_dropFree closedAB.1, unquote_dropFree closedAB.2]
  | var _, closedV => by simp [closed] at closedV
  | drop _ _, closedD => by simp [closed] at closedD

theorem quote_injective {s t : Expr} (freeS : s.dropFree) (freeT : t.dropFree)
    (same : quote s = quote t) : s = t := by
  rw [← unquote_quote freeS, ← unquote_quote freeT, same]

/-- **Filling a quotation instantiates the term's unknowns by the environment's entries.** -/
theorem fill_quote (e : Expr) : ∀ {t : Expr}, t.dropFree →
    fill e (quote t) = subst (fun v => pick v e) t
  | var _, _ => rfl
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [quote, fill, subst]
      rw [fill_quote e free.1, fill_quote e free.2]
  | drop _ _, free => by simp [dropFree] at free

/-- **Dropping a quotation at an environment.** -/
theorem nf_drop_quote {t : Expr} (free : t.dropFree) (e : Expr) :
    nf (drop (quote t) e) = subst (fun v => pick v (nf e)) t := by
  show inst (nf (quote t)) (nf e) = _
  rw [nf_of_closed (quote_closed free), inst, if_pos (quote_closed free), fill_quote _ free]

/-- On drop-free terms, normal forms go inside substitutions. -/
theorem nf_subst_dropFree (σ : ℕ → Expr) : ∀ {t : Expr}, t.dropFree →
    nf (subst σ t) = subst (fun v => nf (σ v)) t
  | var _, _ => rfl
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [subst, nf]
      rw [nf_subst_dropFree σ free.1, nf_subst_dropFree σ free.2]
  | drop _ _, free => by simp [dropFree] at free

theorem nf_pick_of_nf : ∀ {e : Expr}, nf e = e → ∀ i : ℕ, nf (pick i e) = pick i e
  | cell a rest, normal, 0 => by
      simp only [nf, Expr.cell.injEq] at normal
      simpa using normal.1
  | cell a rest, normal, i + 1 => by
      simp only [nf, Expr.cell.injEq] at normal
      simpa using nf_pick_of_nf normal.2 i
  | var v, normal, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i, nf_drop_slot, normal,
        pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
  | sym k, normal, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i, nf_drop_slot, normal,
        pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
  | slot n j, normal, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i, nf_drop_slot, normal,
        pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]
  | drop c d, normal, i => by
      rw [pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i, nf_drop_slot, normal,
        pick_of_not_cell (fun _ _ h => Expr.noConfusion h) i]

/-! ## Lists, environments and tags -/

/-- The symbol ending a list. -/
def nil : Expr := sym 0

/-- A list of terms as a cell list. -/
def lst : List Expr → Expr
  | [] => nil
  | a :: l => cell a (lst l)

theorem pick_lst : ∀ (l : List Expr) (i : ℕ) (inside : i < l.length), pick i (lst l) = l[i]
  | [], _, inside => absurd inside (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, inside => pick_lst l i (Nat.lt_of_succ_lt_succ inside)

theorem nf_lst : ∀ l : List Expr, nf (lst l) = lst (l.map nf)
  | [] => rfl
  | a :: l => by
      show cell (nf a) (nf (lst l)) = _
      rw [nf_lst l]
      rfl

theorem subst_lst (σ : ℕ → Expr) : ∀ l : List Expr, subst σ (lst l) = lst (l.map (subst σ))
  | [] => rfl
  | a :: l => by
      show cell (subst σ a) (subst σ (lst l)) = _
      rw [subst_lst σ l]
      rfl

theorem quote_lst : ∀ l : List Expr, quote (lst l) = lst (l.map quote)
  | [] => rfl
  | a :: l => by
      show cell (quote a) (quote (lst l)) = _
      rw [quote_lst l]
      rfl

theorem closed_lst : ∀ {l : List Expr}, (∀ a ∈ l, a.closed) → (lst l).closed
  | [], _ => rfl
  | a :: l, all => by
      simp only [lst, closed, Bool.and_eq_true]
      exact ⟨all a List.mem_cons_self, closed_lst fun b inside => all b (List.mem_cons_of_mem a inside)⟩

theorem lst_injective : ∀ {l l' : List Expr}, lst l = lst l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, same => Expr.noConfusion same
  | _ :: _, [], same => Expr.noConfusion same
  | a :: l, b :: l', same => by
      simp only [lst, Expr.cell.injEq] at same
      rw [same.1, lst_injective same.2]

/-- **An environment of length `m` holding the values of `h`.** -/
def envOf (h : ℕ → Expr) (m : ℕ) : Expr := lst ((List.range m).map h)

theorem pick_nf_envOf (h : ℕ → Expr) {m v : ℕ} (inside : v < m) :
    pick v (nf (envOf h m)) = nf (h v) := by
  rw [envOf, nf_lst, pick_lst _ _ (by simpa using inside)]
  simp

/-- A data row. -/
def obj (t : Expr) : Expr := cell (sym 1) t

/-- A stored rule's row. -/
def code (c : Expr) : Expr := cell (sym 2) c

theorem nf_obj (t : Expr) : nf (obj t) = obj (nf t) := rfl

theorem nf_code (c : Expr) : nf (code c) = code (nf c) := rfl

theorem subst_obj (σ : ℕ → Expr) (t : Expr) : subst σ (obj t) = obj (subst σ t) := rfl

theorem subst_code (σ : ℕ → Expr) (c : Expr) : subst σ (code c) = code (subst σ c) := rfl

/-- **The tags never meet.** -/
theorem obj_ne_code (t c : Expr) : obj t ≠ code c := by
  intro same
  simp only [obj, code, Expr.cell.injEq, Expr.sym.injEq] at same
  exact absurd same.1 (by decide)

end Expr

#print axioms Expr.nf_subst_nf
#print axioms Expr.action
#print axioms Expr.nf_drop_quote
#print axioms Expr.nf_subst_dropFree
#print axioms Expr.pick_nf_envOf
#print axioms Expr.quote_unquote
#print axioms Expr.subst_congr

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows
