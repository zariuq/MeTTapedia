import Mathlib.Data.List.Forall2
import Mathlib.Data.Option.NAry

/-!
# Open-cons list cells on the PeTTa lane

PeTTa reads every expression as a list.  To share tails, CeTTa also builds
lists from cells: the three-element expression `(tag h t)`, headed by an
internal carrier tag, is the list with head `h` and tail `t`, where `t` is
another cell, an expression, or a variable.  The reference semantics is
SWI-PeTTa's: every expression is a Prolog list, a cell is a cons, a bare tag
reads as nothing, and unification is unification of the readings under a
substitution of reference terms.  A substitution of CeTTa terms represents one
when each of its images has a reading.

A matcher that treats a cell as an ordinary three-element expression disagrees
with the reference: it binds a variable to the tag, and it rejects a flat list
against the cell of the same list.  On tag-free terms the two agree.  Each
decomposition step of the cell-aware worklist matcher
(`petta_semantics_match_cons_constraint`) preserves the reference unifiers
exactly, so the matcher is correct up to its fuel: a solution represents a
reference unifier of its input, and a clash means that no unifier exists.

A value whose chains of cells all end in flat lists needs no such matcher: its
flat form reads as the value does and holds no tag, so structural matching
against it decides unification of the readings (`flat_value_exact`).  Only a
partial list, a chain ending in a variable, keeps its cells.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ListCells

/-! ## Terms and their readings -/

/-- A CeTTa term on the PeTTa lane: `tag` is the internal carrier atom. -/
inductive Tm
  | sym (s : ℕ)
  | var (v : ℕ)
  | tag
  | expr (xs : List Tm)
  deriving Repr

/-- A term of the reference semantics, where every expression is a list. -/
inductive PT
  | atom (s : ℕ)
  | var (v : ℕ)
  | nil
  | cons (h t : PT)
  deriving DecidableEq, Repr

/-- A cons of two optional terms exists only as the cons of two terms. -/
theorem PT.map₂_cons_eq_some {a b : Option PT} {p : PT} (h : Option.map₂ cons a b = some p) :
    ∃ x y, a = some x ∧ b = some y ∧ p = cons x y := by
  cases a with
  | none => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y => cases h; exact ⟨x, y, rfl, rfl, rfl⟩

theorem exists_map₂_cons {a b : Option PT} :
    (∃ p, Option.map₂ PT.cons a b = some p) ↔ (∃ p, a = some p) ∧ ∃ q, b = some q :=
  ⟨fun ⟨_, h⟩ =>
    let ⟨x, y, hx, hy, _⟩ := PT.map₂_cons_eq_some h
    ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
  fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ⟨.cons x y, by rw [hx, hy]; rfl⟩⟩

namespace Tm

/-- The cell with head `h` and tail `t`. -/
@[match_pattern] def cell (h t : Tm) : Tm := expr [tag, h, t]

/-- The carrier test `petta_semantics_is_open_cons_value`. -/
def IsCell (a : Tm) : Prop := ∃ h t, a = cell h t

instance : DecidablePred IsCell := fun a =>
  match a with
  | cell h t => isTrue ⟨h, t, rfl⟩
  | sym _ | var _ | tag | expr [] | expr [_] | expr [_, _] | expr [sym _, _, _]
  | expr [var _, _, _] | expr [expr _, _, _] | expr (_ :: _ :: _ :: _ :: _) =>
    isFalse fun ⟨_, _, e⟩ => by cases e

/-- Every term is a variable, a symbol, the tag, a cell, or a flat expression. -/
theorem view (a : Tm) :
    (∃ x, a = var x) ∨ (∃ s, a = sym s) ∨ a = tag ∨ (∃ h t, a = cell h t) ∨
      ∃ xs, a = expr xs ∧ ¬ IsCell (expr xs) := by
  cases a with
  | var x => exact .inl ⟨x, rfl⟩
  | sym s => exact .inr (.inl ⟨s, rfl⟩)
  | tag => exact .inr (.inr (.inl rfl))
  | expr xs =>
    by_cases hc : IsCell (expr xs)
    · exact .inr (.inr (.inr (.inl hc)))
    · exact .inr (.inr (.inr (.inr ⟨xs, rfl, hc⟩)))

/-- Induction with a hypothesis for every element of an expression. -/
@[elab_as_elim]
theorem induction {motive : Tm → Prop} (sym : ∀ s, motive (.sym s))
    (var : ∀ v, motive (.var v)) (tag : motive .tag)
    (expr : ∀ xs, (∀ x ∈ xs, motive x) → motive (.expr xs)) (t : Tm) : motive t :=
  Tm.rec (motive_1 := motive) (motive_2 := fun xs => ∀ x ∈ xs, motive x) sym var tag expr
    (fun _ h => nomatch h)
    (fun _ _ hx hxs _ h => by
      rcases List.mem_cons.mp h with rfl | h
      exacts [hx, hxs _ h]) t

/-- The elements of a flat list as a chain of cells ending in the empty
expression. -/
def spine : List Tm → Tm
  | [] => expr []
  | x :: xs => cell x (spine xs)

mutual
/-- The reading of a term: a cell is a cons, any other expression the proper
list of its elements, and a bare tag has no reading. -/
def denote : Tm → Option PT
  | sym s => some (.atom s)
  | var v => some (.var v)
  | tag => none
  | cell h t => Option.map₂ .cons h.denote t.denote
  | expr xs => denoteList xs
/-- The proper list of the elements' readings. -/
def denoteList : List Tm → Option PT
  | [] => some .nil
  | x :: xs => Option.map₂ .cons x.denote (denoteList xs)
end

theorem denote_cell (h t : Tm) :
    (cell h t).denote = Option.map₂ .cons h.denote t.denote := rfl

theorem denoteList_cons (x : Tm) (xs : List Tm) :
    denoteList (x :: xs) = Option.map₂ .cons x.denote (denoteList xs) := rfl

theorem denote_expr {xs : List Tm} (hc : ¬ IsCell (expr xs)) :
    (expr xs).denote = denoteList xs :=
  denote.eq_5 xs fun h t e => hc ⟨h, t, by rw [e]; rfl⟩

theorem denote_spine (xs : List Tm) : (spine xs).denote = denoteList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [spine, denote_cell, ih, denoteList_cons]

theorem denoteList_eq_some {xs : List Tm} {q : PT} (h : denoteList xs = some q) :
    q = .nil ∨ ∃ a b, q = .cons a b := by
  cases xs with
  | nil => cases h; exact .inl rfl
  | cons x xs =>
    obtain ⟨a, b, -, -, rfl⟩ := PT.map₂_cons_eq_some h
    exact .inr ⟨a, b, rfl⟩

/-- An expression reads as the empty list or as a cons. -/
theorem denote_expr_eq_some {xs : List Tm} {q : PT} (h : (expr xs).denote = some q) :
    q = .nil ∨ ∃ a b, q = .cons a b := by
  by_cases hc : IsCell (expr xs)
  · obtain ⟨a, b, e⟩ := hc
    rw [e, denote_cell] at h
    obtain ⟨pa, pb, -, -, rfl⟩ := PT.map₂_cons_eq_some h
    exact .inr ⟨pa, pb, rfl⟩
  · exact denoteList_eq_some (by rwa [denote_expr hc] at h)

/-- Only a variable reads as a variable. -/
theorem eq_var_of_denote {t : Tm} {x : ℕ} (h : t.denote = some (.var x)) : t = var x := by
  rcases view t with ⟨y, rfl⟩ | ⟨s, rfl⟩ | rfl | ⟨a, b, rfl⟩ | ⟨xs, rfl, -⟩
  · cases h; rfl
  · cases h
  · cases h
  · obtain ⟨_, _, -, -, e⟩ := PT.map₂_cons_eq_some h; cases e
  · rcases denote_expr_eq_some h with e | ⟨_, _, e⟩ <;> cases e

/-- A term is well formed when it has a reading. -/
def WellFormed (t : Tm) : Prop := ∃ p, t.denote = some p

/-- A flat list has a reading exactly when each element has one. -/
theorem wellFormed_denoteList {xs : List Tm} :
    (∃ p, denoteList xs = some p) ↔ ∀ x ∈ xs, WellFormed x := by
  induction xs with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => ⟨_, rfl⟩⟩
  | cons x xs ih =>
    rw [denoteList_cons, exists_map₂_cons, ih, List.forall_mem_cons]
    exact Iff.rfl

theorem wellFormed_cell {h t : Tm} : WellFormed (cell h t) ↔ WellFormed h ∧ WellFormed t :=
  exists_map₂_cons

theorem wellFormed_flat {xs : List Tm} (hc : ¬ IsCell (expr xs)) :
    WellFormed (expr xs) ↔ ∀ x ∈ xs, WellFormed x := by
  rw [WellFormed, denote_expr hc]
  exact wellFormed_denoteList

theorem wellFormed_spine {xs : List Tm} : WellFormed (spine xs) ↔ ∀ x ∈ xs, WellFormed x := by
  rw [WellFormed, denote_spine]
  exact wellFormed_denoteList

end Tm

open Tm

/-! ## Substitution -/

/-- Substitution in the reference semantics. -/
def PT.subst (θ : ℕ → PT) : PT → PT
  | atom s => atom s
  | var v => θ v
  | nil => nil
  | cons h t => cons (h.subst θ) (t.subst θ)

theorem PT.subst_subst (ρ θ : ℕ → PT) (p : PT) :
    (p.subst ρ).subst θ = p.subst fun w => (ρ w).subst θ := by
  induction p with
  | cons h t ih₁ ih₂ => exact congrArg₂ cons ih₁ ih₂
  | _ => rfl

theorem map₂_cons_map (θ : ℕ → PT) (a b : Option PT) :
    Option.map₂ PT.cons (a.map (PT.subst θ)) (b.map (PT.subst θ)) =
      (Option.map₂ PT.cons a b).map (PT.subst θ) := by
  cases a <;> cases b <;> rfl

namespace Tm

mutual
/-- Substitution on the C encoding: every expression, a cell included, is
rebuilt element by element. -/
def subst (σ : ℕ → Tm) : Tm → Tm
  | sym s => sym s
  | var v => σ v
  | tag => tag
  | expr xs => expr (substList σ xs)
def substList (σ : ℕ → Tm) : List Tm → List Tm
  | [] => []
  | x :: xs => x.subst σ :: substList σ xs
end

theorem subst_expr (σ : ℕ → Tm) (xs : List Tm) :
    (expr xs).subst σ = expr (xs.map (subst σ)) := by
  suffices ∀ xs, substList σ xs = xs.map (subst σ) from congrArg expr (this xs)
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x.subst σ :: ·) ih

theorem subst_cell (σ : ℕ → Tm) (h t : Tm) :
    (cell h t).subst σ = cell (h.subst σ) (t.subst σ) := rfl

/-- Substitution by images other than the bare tag makes no new cell. -/
theorem not_isCell_subst {σ : ℕ → Tm} (hσ : ∀ v, σ v ≠ tag) {xs : List Tm}
    (hc : ¬ IsCell (expr xs)) : ¬ IsCell (expr (xs.map (subst σ))) := by
  rintro ⟨h, t, e⟩
  change expr _ = expr [tag, h, t] at e
  rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, xs⟩⟩⟩⟩ <;> simp at e
  obtain ⟨e, -, -⟩ := e
  cases x with
  | var v => exact hσ v e
  | tag => exact hc ⟨y, z, rfl⟩
  | sym => cases e
  | expr => cases e

mutual
/-- Whether `x` occurs in a term: the loop check of variable binding. -/
def occurs (x : ℕ) : Tm → Bool
  | sym _ => false
  | var v => v == x
  | tag => false
  | expr xs => occursList x xs
def occursList (x : ℕ) : List Tm → Bool
  | [] => false
  | y :: ys => y.occurs x || occursList x ys
end

theorem occursList_eq_false {x : ℕ} {xs : List Tm} :
    occursList x xs = false ↔ ∀ y ∈ xs, y.occurs x = false := by
  induction xs with
  | nil => simp [occursList]
  | cons y ys ih => simp [occursList, ih]

/-- A binding leaves alone a term its variable does not occur in. -/
theorem subst_update_of_not_occurs {x : ℕ} {s : Tm} :
    ∀ t : Tm, t.occurs x = false → t.subst (Function.update var x s) = t := by
  intro t
  induction t using Tm.induction with
  | sym => intro; rfl
  | var v => intro h; exact Function.update_of_ne (by simpa [occurs] using h) _ _
  | tag => intro; rfl
  | expr xs ih =>
    intro h
    rw [subst_expr, List.map_congr_left fun y hy => ih y hy (occursList_eq_false.mp h y hy),
      List.map_id']

end Tm

/-- A C substitution represents a reference one when each image has that
reading. -/
def Represents (σ : ℕ → Tm) (θ : ℕ → PT) : Prop := ∀ v, (σ v).denote = some (θ v)

/-- Reading commutes with a substitution that represents a reference one.  A
substitution that plants a bare tag need not commute (see the controls). -/
theorem denote_subst {σ : ℕ → Tm} {θ : ℕ → PT} (hσ : Represents σ θ) (t : Tm) :
    (t.subst σ).denote = t.denote.map (PT.subst θ) := by
  have untagged : ∀ v, σ v ≠ tag := fun v e => by simpa [e, denote] using hσ v
  induction t using Tm.induction with
  | sym => rfl
  | var v => exact hσ v
  | tag => rfl
  | expr xs ih =>
    by_cases hc : IsCell (expr xs)
    · obtain ⟨h, t, e⟩ := hc
      cases e
      show (cell (h.subst σ) (t.subst σ)).denote = (cell h t).denote.map _
      rw [denote_cell, denote_cell, ih h (by simp), ih t (by simp), map₂_cons_map]
    · rw [subst_expr, denote_expr (not_isCell_subst untagged hc), denote_expr hc]
      clear hc
      induction xs with
      | nil => rfl
      | cons x xs ihx =>
        rw [List.map_cons, denoteList_cons, denoteList_cons, ih x (List.mem_cons_self ..),
          ihx fun y hy => ih y (List.mem_cons_of_mem x hy), map₂_cons_map]

theorem represents_update {x : ℕ} {t : Tm} {p : PT} (ht : t.denote = some p) :
    Represents (Function.update var x t) (Function.update PT.var x p) := fun w => by
  rw [Function.update_apply, Function.update_apply]
  split_ifs
  exacts [ht, rfl]

/-! ## Unification in the reference semantics -/

/-- Two optional readings agree under `θ`: both exist and `θ` equates them. -/
def Agree (θ : ℕ → PT) (a b : Option PT) : Prop :=
  ∃ p q, a = some p ∧ b = some q ∧ p.subst θ = q.subst θ

/-- `θ` unifies `a` and `b` in the reference semantics. -/
def Unifies (θ : ℕ → PT) (a b : Tm) : Prop := Agree θ a.denote b.denote

theorem Agree.symm {θ : ℕ → PT} {a b : Option PT} : Agree θ a b → Agree θ b a :=
  fun ⟨p, q, hp, hq, e⟩ => ⟨q, p, hq, hp, e.symm⟩

theorem unifies_comm {θ : ℕ → PT} {a b : Tm} : Unifies θ a b ↔ Unifies θ b a :=
  ⟨Agree.symm, Agree.symm⟩

theorem agree_map₂_cons {θ : ℕ → PT} {a b c d : Option PT} :
    Agree θ (Option.map₂ .cons a b) (Option.map₂ .cons c d) ↔ Agree θ a c ∧ Agree θ b d := by
  constructor
  · rintro ⟨p, q, hp, hq, e⟩
    obtain ⟨x, y, rfl, rfl, rfl⟩ := PT.map₂_cons_eq_some hp
    obtain ⟨z, w, rfl, rfl, rfl⟩ := PT.map₂_cons_eq_some hq
    injection e with e₁ e₂
    exact ⟨⟨x, z, rfl, rfl, e₁⟩, ⟨y, w, rfl, rfl, e₂⟩⟩
  · rintro ⟨⟨x, z, rfl, rfl, e₁⟩, ⟨y, w, rfl, rfl, e₂⟩⟩
    exact ⟨_, _, rfl, rfl, congrArg₂ PT.cons e₁ e₂⟩

theorem agree_map {ρ θ : ℕ → PT} {a b : Option PT} :
    Agree θ (a.map (PT.subst ρ)) (b.map (PT.subst ρ)) ↔
      Agree (fun w => (ρ w).subst θ) a b := by
  cases a <;> cases b <;> simp [Agree, PT.subst_subst]

/-- Instantiating by a represented substitution, then unifying, is unifying
with the composite. -/
theorem unifies_subst {ρ : ℕ → Tm} {ρ' : ℕ → PT} (hρ : Represents ρ ρ') (θ : ℕ → PT)
    (a b : Tm) :
    Unifies θ (a.subst ρ) (b.subst ρ) ↔ Unifies (fun w => (ρ' w).subst θ) a b := by
  unfold Unifies
  rw [denote_subst hρ, denote_subst hρ, agree_map]

theorem unifies_var {θ : ℕ → PT} {x : ℕ} {t : Tm} :
    Unifies θ (var x) t ↔ ∃ q, t.denote = some q ∧ θ x = q.subst θ :=
  ⟨fun ⟨_, q, hp, hq, e⟩ => by cases hp; exact ⟨q, hq, e⟩,
    fun ⟨q, hq, e⟩ => ⟨_, q, rfl, hq, e⟩⟩

/-! ## The defect -/

/-- `[1, 2, 3]` as CeTTa builds it: a cell whose tail is the flat list `(2 3)`. -/
def list123 : Tm := cell (sym 1) (expr [sym 2, sym 3])

/-- The flat pattern `($0 $1 $2)`. -/
def pattern3 : Tm := expr [var 0, var 1, var 2]

/-- Structurally the cell is a three-element expression: the unifiers with the
pattern are exactly those binding `$0` to the carrier tag. -/
theorem structural_unifiers_iff (σ : ℕ → Tm) :
    pattern3.subst σ = list123.subst σ ↔
      σ 0 = tag ∧ σ 1 = sym 1 ∧ σ 2 = expr [sym 2, sym 3] := by
  change expr [σ 0, σ 1, σ 2] = expr [tag, sym 1, expr [sym 2, sym 3]] ↔ _
  simp

/-- In the reference semantics the unifiers bind `$0 $1 $2` to `1 2 3`. -/
theorem reference_unifiers_iff (θ : ℕ → PT) :
    Unifies θ pattern3 list123 ↔ θ 0 = .atom 1 ∧ θ 1 = .atom 2 ∧ θ 2 = .atom 3 := by
  change Agree θ (some (.cons (.var 0) (.cons (.var 1) (.cons (.var 2) .nil))))
    (some (.cons (.atom 1) (.cons (.atom 2) (.cons (.atom 3) .nil)))) ↔ _
  simp [Agree, PT.subst]

/-- The defect: structural matching of `($0 $1 $2)` against the cell of
`[1, 2, 3]` succeeds, but only by binding `$0` to the tag, so no structural
unifier represents a reference substitution; the reference unifiers exist and
bind `$0` to `1`. -/
theorem structural_matching_disagrees :
    (∃ σ, pattern3.subst σ = list123.subst σ) ∧
      (∀ σ θ, pattern3.subst σ = list123.subst σ → ¬ Represents σ θ) ∧
      (∃ θ, Unifies θ pattern3 list123) ∧
      ∀ θ, Unifies θ pattern3 list123 → θ 0 = .atom 1 := by
  refine ⟨⟨fun v => [tag, sym 1, expr [sym 2, sym 3]].getD v (var v), rfl⟩,
    fun σ θ e hσ => ?_, ⟨fun v => [.atom 1, .atom 2, .atom 3].getD v (.var v),
      (reference_unifiers_iff _).mpr ⟨rfl, rfl, rfl⟩⟩,
    fun θ hu => ((reference_unifiers_iff θ).mp hu).1⟩
  have h0 := hσ 0
  rw [((structural_unifiers_iff σ).mp e).1] at h0
  cases h0

/-- The flat list `(1 2 3)` reads as the cell of `[1, 2, 3]`, yet no
substitution makes the two structurally equal. -/
theorem literal_fails_structurally :
    (expr [sym 1, sym 2, sym 3]).denote = list123.denote ∧
      ∀ σ, (expr [sym 1, sym 2, sym 3]).subst σ ≠ list123.subst σ :=
  ⟨rfl, fun _ e => by cases e⟩

/-- `[1, 2]` as a cell. -/
def list12 : Tm := cell (sym 1) (expr [sym 2])

/-- A two-element pattern against a cell: structurally the arities differ; in
the reference the pattern binds `$0 $1` to `1 2`. -/
theorem two_element_pattern :
    (∀ σ, (expr [var 0, var 1]).subst σ ≠ list12.subst σ) ∧
      ∀ θ, Unifies θ (expr [var 0, var 1]) list12 ↔ θ 0 = .atom 1 ∧ θ 1 = .atom 2 := by
  refine ⟨fun σ e => ?_, fun θ => ?_⟩
  · change expr [σ 0, σ 1] = expr [tag, sym 1, expr [sym 2]] at e
    simp at e
  · change Agree θ (some (.cons (.var 0) (.cons (.var 1) .nil)))
      (some (.cons (.atom 1) (.cons (.atom 2) .nil))) ↔ _
    simp [Agree, PT.subst]

/-! ## Tag-free terms -/

namespace Tm

/-- No carrier tag anywhere. -/
inductive TagFree : Tm → Prop
  | sym (s : ℕ) : TagFree (sym s)
  | var (v : ℕ) : TagFree (var v)
  | expr (xs : List Tm) : (∀ x ∈ xs, TagFree x) → TagFree (expr xs)

namespace TagFree

theorem not_isCell {a : Tm} (ha : TagFree a) : ¬ IsCell a := by
  rintro ⟨h, t, rfl⟩
  cases ha with
  | expr _ hxs => nomatch hxs tag (by simp)

/-- The reading is compositional on tag-free expressions: the proper list of
the elements' readings. -/
theorem denote_expr {xs : List Tm} (h : TagFree (Tm.expr xs)) :
    (Tm.expr xs).denote = denoteList xs :=
  Tm.denote_expr h.not_isCell

/-- A tag-free term has a reading. -/
theorem wellFormed {a : Tm} (ha : TagFree a) : WellFormed a := by
  induction ha with
  | sym => exact ⟨_, rfl⟩
  | var => exact ⟨_, rfl⟩
  | expr xs hxs ih =>
    rw [WellFormed, (TagFree.expr xs hxs).denote_expr]
    exact wellFormed_denoteList.mpr ih

theorem subst {a : Tm} {σ : ℕ → Tm} (ha : TagFree a) (hσ : ∀ v, TagFree (σ v)) :
    TagFree (a.subst σ) := by
  induction ha with
  | sym s => exact .sym s
  | var v => exact hσ v
  | expr xs _ ih =>
    rw [subst_expr]
    refine .expr _ fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact ih x hx

theorem map₂_cons_inj {a b c d : Option PT} (ha : ∃ p, a = some p) (hb : ∃ q, b = some q)
    (e : Option.map₂ PT.cons a b = Option.map₂ PT.cons c d) : a = c ∧ b = d := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  obtain ⟨z, w, rfl, rfl, h⟩ := PT.map₂_cons_eq_some e.symm
  injection h with h₁ h₂
  exact ⟨congrArg some h₁, congrArg some h₂⟩

/-- On tag-free terms the reading is injective. -/
theorem denote_injective :
    ∀ {a b : Tm}, TagFree a → TagFree b → a.denote = b.denote → a = b := by
  intro a
  induction a using Tm.induction with
  | sym s =>
    intro b _ hb e
    cases hb with
    | sym => cases e; rfl
    | var => cases e
    | expr => rcases denote_expr_eq_some e.symm with h | ⟨_, _, h⟩ <;> cases h
  | var v =>
    intro b _ hb e
    cases hb with
    | sym => cases e
    | var => cases e; rfl
    | expr => rcases denote_expr_eq_some e.symm with h | ⟨_, _, h⟩ <;> cases h
  | tag => intro _ ha; nomatch ha
  | expr xs ih =>
    intro b ha hb e
    cases hb with
    | sym => rcases denote_expr_eq_some e with h | ⟨_, _, h⟩ <;> cases h
    | var => rcases denote_expr_eq_some e with h | ⟨_, _, h⟩ <;> cases h
    | expr ys hys =>
      cases ha with
      | expr _ hxs =>
      rw [(TagFree.expr xs hxs).denote_expr, (TagFree.expr ys hys).denote_expr] at e
      congr 1
      induction xs generalizing ys with
      | nil =>
        cases ys with
        | nil => rfl
        | cons =>
          obtain ⟨_, _, -, -, h⟩ := PT.map₂_cons_eq_some e.symm
          cases h
      | cons x xs ihx =>
        cases ys with
        | nil =>
          obtain ⟨_, _, -, -, h⟩ := PT.map₂_cons_eq_some e
          cases h
        | cons y ys =>
          obtain ⟨hx, hxs⟩ := List.forall_mem_cons.mp hxs
          obtain ⟨hy, hys⟩ := List.forall_mem_cons.mp hys
          obtain ⟨e₁, e₂⟩ := map₂_cons_inj hx.wellFormed
            (wellFormed_denoteList.mpr fun z hz => (hxs z hz).wellFormed) e
          rw [ih x (List.mem_cons_self ..) hx hy e₁,
            ihx (fun z hz => ih z (List.mem_cons_of_mem _ hz)) ys hys e₂ hxs]

end TagFree

end Tm

/-- On tag-free terms and substitutions, structural unification is unification
of the readings. -/
theorem subst_eq_iff_unifies {a b : Tm} {σ : ℕ → Tm} {θ : ℕ → PT} (ha : TagFree a)
    (hb : TagFree b) (hσ : ∀ v, TagFree (σ v)) (hθ : Represents σ θ) :
    a.subst σ = b.subst σ ↔ Unifies θ a b := by
  obtain ⟨p, hp⟩ := ha.wellFormed
  obtain ⟨q, hq⟩ := hb.wellFormed
  have ea : (a.subst σ).denote = some (p.subst θ) := by rw [denote_subst hθ, hp]; rfl
  have eb : (b.subst σ).denote = some (q.subst θ) := by rw [denote_subst hθ, hq]; rfl
  constructor
  · intro e
    exact ⟨p, q, hp, hq, Option.some.inj (ea.symm.trans ((congrArg denote e).trans eb))⟩
  · rintro ⟨p', q', hp', hq', e⟩
    rw [hp] at hp'
    rw [hq] at hq'
    cases hp'
    cases hq'
    exact (ha.subst hσ).denote_injective (hb.subst hσ)
      (ea.trans ((congrArg some e).trans eb.symm))

/-! ## Flat forms

`petta_semantics_materialize_value` replaces each chain of cells that ends in
a flat list by the flat list of its elements.  On a term whose chains all end
in flat lists, the result reads as the term does and holds no tag, so
structural matching against it decides unification of the readings exactly.
A chain ending in a variable is a partial list: it has no flat form. -/

namespace Tm

/-- A head before an already flattened tail: the flat list when the tail is a
flat list and the result is no cell, the cell otherwise. -/
def flatCons (h : Tm) : Tm → Tm
  | sym s => cell h (sym s)
  | var v => cell h (var v)
  | tag => cell h tag
  | expr ys => if IsCell (expr ys) ∨ IsCell (expr (h :: ys)) then cell h (expr ys)
      else expr (h :: ys)

mutual
/-- `petta_semantics_materialize_value`. -/
def flat : Tm → Tm
  | sym s => sym s
  | var v => var v
  | tag => tag
  | cell h t => flatCons h.flat t.flat
  | expr xs => expr (flatList xs)
/-- The elements' flat forms. -/
def flatList : List Tm → List Tm
  | [] => []
  | x :: xs => x.flat :: flatList xs
end

theorem flat_cell (h t : Tm) : (cell h t).flat = flatCons h.flat t.flat := rfl

theorem flat_expr {xs : List Tm} (hc : ¬ IsCell (expr xs)) :
    (expr xs).flat = expr (flatList xs) :=
  flat.eq_5 xs fun h t e => hc ⟨h, t, by rw [e]; rfl⟩

theorem flatList_eq_map (xs : List Tm) : flatList xs = xs.map flat := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [flatList, ih]; rfl

/-- A cell of `h` and `t` reads as the cons of their readings, flattened or
not. -/
theorem denote_flatCons (h t : Tm) :
    (flatCons h t).denote = Option.map₂ .cons h.denote t.denote := by
  cases t with
  | sym s => rfl
  | var v => rfl
  | tag => rfl
  | expr ys =>
    rw [flatCons]
    by_cases hc : IsCell (expr ys) ∨ IsCell (expr (h :: ys))
    · rw [if_pos hc]; rfl
    · rw [if_neg hc]
      obtain ⟨hys, hhys⟩ := not_or.mp hc
      rw [denote_expr hhys, denoteList_cons, denote_expr hys]

theorem flatCons_isExpr (h t : Tm) : ∃ zs, flatCons h t = expr zs := by
  cases t with
  | sym s => exact ⟨_, rfl⟩
  | var v => exact ⟨_, rfl⟩
  | tag => exact ⟨_, rfl⟩
  | expr ys =>
    rw [flatCons]
    by_cases hc : IsCell (expr ys) ∨ IsCell (expr (h :: ys))
    · rw [if_pos hc]; exact ⟨_, rfl⟩
    · rw [if_neg hc]; exact ⟨_, rfl⟩

/-- Only the tag flattens to the tag. -/
theorem eq_tag_of_flat {x : Tm} (h : x.flat = tag) : x = tag := by
  rcases view x with ⟨v, rfl⟩ | ⟨s, rfl⟩ | rfl | ⟨a, b, rfl⟩ | ⟨xs, rfl, hc⟩
  · cases h
  · cases h
  · rfl
  · obtain ⟨zs, e⟩ := flatCons_isExpr a.flat b.flat
    rw [flat_cell, e] at h
    cases h
  · rw [flat_expr hc] at h
    cases h

/-- Flattening makes no cell of an expression that is none. -/
theorem not_isCell_flatList {xs : List Tm} (hc : ¬ IsCell (expr xs)) :
    ¬ IsCell (expr (flatList xs)) := by
  rintro ⟨h, t, e⟩
  injection e with e
  rw [flatList_eq_map] at e
  obtain ⟨x, y, z, rfl⟩ :=
    List.length_eq_three.mp (by simpa using congrArg List.length e)
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
  exact hc ⟨y, z, by rw [eq_tag_of_flat e.1]; rfl⟩

theorem denoteList_flatList {xs : List Tm} (ih : ∀ x ∈ xs, x.flat.denote = x.denote) :
    denoteList (flatList xs) = denoteList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ihx =>
    obtain ⟨hx, hxs⟩ := List.forall_mem_cons.mp ih
    rw [flatList, denoteList_cons, denoteList_cons, hx, ihx hxs]

/-- Flattening keeps the reading. -/
theorem denote_flat (a : Tm) : a.flat.denote = a.denote := by
  induction a using Tm.induction with
  | sym s => rfl
  | var v => rfl
  | tag => rfl
  | expr xs ih =>
    by_cases hc : IsCell (expr xs)
    · obtain ⟨h, t, e⟩ := hc
      injection e with exs
      subst exs
      rw [show expr [tag, h, t] = cell h t from rfl, flat_cell, denote_flatCons,
        ih h (by simp), ih t (by simp), denote_cell]
    · rw [flat_expr hc, denote_expr (not_isCell_flatList hc), denote_expr hc]
      exact denoteList_flatList ih

/-- Every chain of cells ends in a flat list, and no bare tag stands
elsewhere: the terms `petta_semantics_value_holds_open_chain` answers false
for. -/
inductive Closed : Tm → Prop
  | sym (s : ℕ) : Closed (sym s)
  | var (v : ℕ) : Closed (var v)
  | cell {h : Tm} {ys : List Tm} : Closed h → Closed (expr ys) → Closed (cell h (expr ys))
  | flat (xs : List Tm) : ¬ IsCell (expr xs) → (∀ x ∈ xs, Closed x) → Closed (expr xs)

theorem TagFree.ne_tag {a : Tm} (ha : TagFree a) : a ≠ tag := by
  rintro rfl
  cases ha

/-- A closed term flattens to a tag-free one. -/
theorem Closed.tagFree_flat {a : Tm} (ha : Closed a) : TagFree a.flat := by
  induction ha with
  | sym s => exact .sym s
  | var v => exact .var v
  | @cell h ys _ _ ihh iht =>
    rw [flat_cell]
    have hz : ∃ zs, (expr ys).flat = expr zs := by
      by_cases hc : IsCell (expr ys)
      · obtain ⟨a, b, e⟩ := hc
        rw [e, flat_cell]
        exact flatCons_isExpr _ _
      · exact ⟨_, flat_expr hc⟩
    obtain ⟨zs, ez⟩ := hz
    rw [ez] at iht ⊢
    have hzs := iht.not_isCell
    have hcons : ¬ IsCell (expr (h.flat :: zs)) := by
      rintro ⟨a, b, e⟩
      injection e with e
      injection e with e₀
      exact ihh.ne_tag e₀
    rw [flatCons, if_neg (not_or.mpr ⟨hzs, hcons⟩)]
    cases iht with
    | expr _ hzs' =>
      refine .expr _ fun y hy => ?_
      rcases List.mem_cons.mp hy with rfl | hy
      exacts [ihh, hzs' y hy]
  | flat xs hc _ ih =>
    rw [flat_expr hc, flatList_eq_map]
    exact .expr _ fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact ih x hx

end Tm

/-- A value whose chains all end in flat lists meets a tag-free pattern
structurally, in its flat form, exactly when the readings unify. -/
theorem flat_value_exact {pattern value : Tm} {σ : ℕ → Tm} {θ : ℕ → PT}
    (hp : TagFree pattern) (hq : Closed value) (hσ : ∀ v, TagFree (σ v))
    (hθ : Represents σ θ) :
    pattern.subst σ = value.flat.subst σ ↔ Unifies θ pattern value := by
  rw [subst_eq_iff_unifies hp hq.tagFree_flat hσ hθ]
  unfold Unifies
  rw [denote_flat]

/-! ## Closed spines

`petta_semantics_closed_list` reads a chain of cells that ends in a flat list
as the one flat list of its elements, which stand as they are: an element that
is itself a chain stays one.  A chain ending in a variable, a symbol or the tag
has no closed spine: it is a partial or improper list.

The list natives that read a spine alone read it so.  The elements read, as a
proper list, as the chain does (`denoteList_closedElems`).  `append` of two
closed spines is the concatenation of their elements, which reads as Prolog's
append/3 of their readings (`denoteList_append`).  `length` is the number of
elements, the length of the reading (`len_denoteList`). -/

namespace Tm

/-- The elements of a closed chain of cells, as they stand. -/
def closedElems : Tm → Option (List Tm)
  | cell h t => (closedElems t).map (h :: ·)
  | expr xs => some xs
  | _ => none

theorem closedElems_cell (h t : Tm) :
    (cell h t).closedElems = t.closedElems.map (h :: ·) := rfl

theorem closedElems_expr {xs : List Tm} (hc : ¬ IsCell (expr xs)) :
    (expr xs).closedElems = some xs :=
  closedElems.eq_2 xs fun h t e => hc ⟨h, t, by rw [e]; rfl⟩

/-- A closed spine's elements read, as a proper list, as the chain does. -/
theorem denoteList_closedElems {t : Tm} :
    ∀ {xs : List Tm}, t.closedElems = some xs → denoteList xs = t.denote := by
  induction t using Tm.induction with
  | sym s => intro xs h; cases h
  | var v => intro xs h; cases h
  | tag => intro xs h; cases h
  | expr ys ih =>
    intro xs h
    by_cases hc : IsCell (expr ys)
    · obtain ⟨a, b, e⟩ := hc
      have hys : ys = [tag, a, b] := by injection e
      subst hys
      rw [show expr [tag, a, b] = cell a b from rfl, closedElems_cell] at h
      obtain ⟨zs, hzs, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [denoteList_cons, ih b (by simp) hzs]
      rfl
    · rw [closedElems_expr hc] at h
      cases h
      exact (denote_expr hc).symm

end Tm

/-- A proper list with its final `nil` replaced by `q`: Prolog's append/3 of
a proper list and `q`.  Every reading of a flat list is proper, so the last
case, an improper tail, does not arise below. -/
def PT.graft : PT → PT → PT
  | .cons a b, q => .cons a (b.graft q)
  | .nil, q => q
  | p, _ => p

/-- The concatenation of two lists of elements reads as the append of their
readings. -/
theorem denoteList_append (xs ys : List Tm) :
    denoteList (xs ++ ys) = Option.map₂ PT.graft (denoteList xs) (denoteList ys) := by
  induction xs with
  | nil =>
    rw [List.nil_append]
    cases denoteList ys <;> rfl
  | cons x xs ih =>
    rw [List.cons_append, denoteList_cons, ih, denoteList_cons]
    cases x.denote <;> cases denoteList xs <;> cases denoteList ys <;> rfl

/-- The length of a proper list. -/
def PT.len : PT → Option ℕ
  | .nil => some 0
  | .cons _ b => b.len.map (· + 1)
  | _ => none

/-- A list of elements with a reading has as many elements as its reading. -/
theorem len_denoteList :
    ∀ {xs : List Tm} {p : PT}, denoteList xs = some p → p.len = some xs.length
  | [], _, h => by cases h; rfl
  | x :: xs, p, h => by
    rw [denoteList_cons] at h
    obtain ⟨a, q, -, hq, rfl⟩ := PT.map₂_cons_eq_some h
    rw [PT.len, len_denoteList hq]
    rfl

namespace Controls

/-- `[1, 2, 3]` as a cell before the flat list `(2 3)` has the closed spine
`(1 2 3)`, which reads as it does. -/
theorem closed_spine :
    (Tm.cell (.sym 1) (.expr [.sym 2, .sym 3])).closedElems =
        some [.sym 1, .sym 2, .sym 3] ∧
      Tm.denoteList [.sym 1, .sym 2, .sym 3] =
        (Tm.cell (.sym 1) (.expr [.sym 2, .sym 3])).denote :=
  ⟨rfl, rfl⟩

/-- A chain ending in a variable is a partial list: it has no closed spine,
so `append` over it stays relational. -/
theorem partial_no_spine : (Tm.cell (.sym 1) (.var 0)).closedElems = none := rfl

/-- The elements stand as they are: a chain inside a closed spine stays a
chain. -/
theorem elements_stand :
    (Tm.expr [Tm.cell (.sym 1) (.expr [])]).closedElems =
      some [Tm.cell (.sym 1) (.expr [])] := rfl

end Controls

/-! ## Decomposition -/

/-- (a) Two cells unify exactly when their heads unify and their tails unify. -/
theorem unifies_cell_cell (θ : ℕ → PT) (h t h' t' : Tm) :
    Unifies θ (cell h t) (cell h' t') ↔ Unifies θ h h' ∧ Unifies θ t t' :=
  agree_map₂_cons

/-- (b) A cell against a nonempty flat list: the heads, and the tail against
the rest of the list read as a chain of cells. -/
theorem unifies_cell_flat (θ : ℕ → PT) (h t y : Tm) {ys : List Tm}
    (hc : ¬ IsCell (expr (y :: ys))) :
    Unifies θ (cell h t) (expr (y :: ys)) ↔ Unifies θ h y ∧ Unifies θ t (spine ys) := by
  unfold Unifies
  rw [denote_expr hc, denoteList_cons, denote_cell, denote_spine, agree_map₂_cons]

/-- (b) with the flat rest itself, as `petta_semantics_match_cons_constraint`
meets it, through a suffix view of the list's storage: the chain of a flat
list reads as the list, when the rest is no cell. -/
theorem unifies_cell_flat_rest (θ : ℕ → PT) (h t y : Tm) {ys : List Tm}
    (hc : ¬ IsCell (expr (y :: ys))) (hr : ¬ IsCell (expr ys)) :
    Unifies θ (cell h t) (expr (y :: ys)) ↔ Unifies θ h y ∧ Unifies θ t (expr ys) := by
  rw [unifies_cell_flat θ h t y hc]
  unfold Unifies
  rw [denote_spine, denote_expr hr]

/-- The rest of a well-formed flat list is no cell: the cell's tag would be an
element of the list, and a tag has no reading. -/
theorem rest_not_isCell {y : Tm} {ys : List Tm} (hc : ¬ IsCell (expr (y :: ys)))
    (hw : WellFormed (expr (y :: ys))) : ¬ IsCell (expr ys) := by
  rintro ⟨h, t, e⟩
  have hys : ys = [tag, h, t] := Tm.expr.inj e
  obtain ⟨p, hp⟩ := (wellFormed_flat hc).mp hw tag (by simp [hys])
  cases hp

/-- (b) on a well-formed list, as the open-equation tier's list operations meet
a nonempty flat list: the heads, and the tail against the suffix that shares the
list's storage.  The tier checks no side condition: a flat list with a reading
has no cell for its rest. -/
theorem unifies_cell_flat_wellFormed (θ : ℕ → PT) (h t y : Tm) {ys : List Tm}
    (hc : ¬ IsCell (expr (y :: ys))) (hw : WellFormed (expr (y :: ys))) :
    Unifies θ (cell h t) (expr (y :: ys)) ↔ Unifies θ h y ∧ Unifies θ t (expr ys) :=
  unifies_cell_flat_rest θ h t y hc (rest_not_isCell hc hw)

/-- (c) A cell unifies with neither the empty expression nor a symbol. -/
theorem not_unifies_cell_nil (θ : ℕ → PT) (h t : Tm) : ¬ Unifies θ (cell h t) (expr []) := by
  rintro ⟨p, q, hp, hq, e⟩
  obtain ⟨_, _, -, -, rfl⟩ := PT.map₂_cons_eq_some hp
  cases hq
  cases e

theorem not_unifies_cell_sym (θ : ℕ → PT) (h t : Tm) (s : ℕ) :
    ¬ Unifies θ (cell h t) (sym s) := by
  rintro ⟨p, q, hp, hq, e⟩
  obtain ⟨_, _, -, -, rfl⟩ := PT.map₂_cons_eq_some hp
  cases hq
  cases e

theorem agree_denoteList (θ : ℕ → PT) : ∀ xs ys : List Tm,
    Agree θ (denoteList xs) (denoteList ys) ↔ List.Forall₂ (Unifies θ) xs ys
  | [], [] => ⟨fun _ => .nil, fun _ => ⟨_, _, rfl, rfl, rfl⟩⟩
  | [], y :: ys => by
    refine ⟨fun ⟨_, _, hp, hq, e⟩ => ?_, fun h => nomatch h⟩
    rw [denoteList_cons] at hq
    obtain ⟨_, _, -, -, rfl⟩ := PT.map₂_cons_eq_some hq
    cases hp
    cases e
  | x :: xs, [] => by
    refine ⟨fun ⟨_, _, hp, hq, e⟩ => ?_, fun h => nomatch h⟩
    rw [denoteList_cons] at hp
    obtain ⟨_, _, -, -, rfl⟩ := PT.map₂_cons_eq_some hp
    cases hq
    cases e
  | x :: xs, y :: ys => by
    rw [denoteList_cons, denoteList_cons, agree_map₂_cons, agree_denoteList θ xs ys,
      List.forall₂_cons]
    exact Iff.rfl

/-- (d) Two flat lists unify exactly when they have one length and unify
elementwise; the elements may themselves be cells. -/
theorem unifies_flat_flat (θ : ℕ → PT) {xs ys : List Tm} (hx : ¬ IsCell (expr xs))
    (hy : ¬ IsCell (expr ys)) :
    Unifies θ (expr xs) (expr ys) ↔ List.Forall₂ (Unifies θ) xs ys := by
  rw [← agree_denoteList, ← denote_expr hx, ← denote_expr hy]
  exact Iff.rfl

/-- The decompositions of the worklist matcher: a pair is replaced by the pairs
of its parts. -/
inductive Split : Tm → Tm → List (Tm × Tm) → Prop
  | var (x : ℕ) : Split (.var x) (.var x) []
  | sym (s : ℕ) : Split (.sym s) (.sym s) []
  | cell (h t h' t' : Tm) : Split (.cell h t) (.cell h' t') [(h, h'), (t, t')]
  | cellFlat (h t y : Tm) (ys : List Tm) : ¬ IsCell (.expr (y :: ys)) →
      Split (.cell h t) (.expr (y :: ys)) [(h, y), (t, spine ys)]
  | flatCell (x : Tm) (xs : List Tm) (h t : Tm) : ¬ IsCell (.expr (x :: xs)) →
      Split (.expr (x :: xs)) (.cell h t) [(x, h), (spine xs, t)]
  | flat (xs ys : List Tm) : ¬ IsCell (.expr xs) → ¬ IsCell (.expr ys) →
      xs.length = ys.length → Split (.expr xs) (.expr ys) (xs.zip ys)

/-- Every decomposition preserves the reference unifiers exactly. -/
theorem Split.unifies_iff {a b : Tm} {ps : List (Tm × Tm)} (hs : Split a b ps) (θ : ℕ → PT) :
    Unifies θ a b ↔ ∀ e ∈ ps, Unifies θ e.1 e.2 := by
  cases hs with
  | var x => exact ⟨fun _ _ h => (nomatch h), fun _ => ⟨_, _, rfl, rfl, rfl⟩⟩
  | sym s => exact ⟨fun _ _ h => (nomatch h), fun _ => ⟨_, _, rfl, rfl, rfl⟩⟩
  | cell h t h' t' => simp [unifies_cell_cell]
  | cellFlat h t y ys hc => simp [unifies_cell_flat θ h t y hc]
  | flatCell x xs h t hc =>
    rw [unifies_comm, unifies_cell_flat θ h t x hc]
    simp [unifies_comm]
  | flat xs ys hx hy hl =>
    rw [unifies_flat_flat θ hx hy, List.forall₂_iff_zip]
    exact ⟨fun h e he => h.2 he, fun h => ⟨hl, fun he => h _ he⟩⟩

/-- The parts of well-formed terms are well formed. -/
theorem Split.wellFormed {a b : Tm} {ps : List (Tm × Tm)} (hs : Split a b ps)
    (ha : WellFormed a) (hb : WellFormed b) : ∀ e ∈ ps, WellFormed e.1 ∧ WellFormed e.2 := by
  cases hs with
  | var | sym => exact fun _ h => nomatch h
  | cell =>
    obtain ⟨h₁, h₂⟩ := wellFormed_cell.mp ha
    obtain ⟨h₃, h₄⟩ := wellFormed_cell.mp hb
    simp [*]
  | cellFlat h t y ys hc =>
    obtain ⟨h₁, h₂⟩ := wellFormed_cell.mp ha
    obtain ⟨h₃, h₄⟩ := List.forall_mem_cons.mp ((wellFormed_flat hc).mp hb)
    exact List.forall_mem_cons.mpr
      ⟨⟨h₁, h₃⟩, List.forall_mem_singleton.mpr ⟨h₂, wellFormed_spine.mpr h₄⟩⟩
  | flatCell x xs h t hc =>
    obtain ⟨h₁, h₂⟩ := List.forall_mem_cons.mp ((wellFormed_flat hc).mp ha)
    obtain ⟨h₃, h₄⟩ := wellFormed_cell.mp hb
    exact List.forall_mem_cons.mpr
      ⟨⟨h₁, h₃⟩, List.forall_mem_singleton.mpr ⟨wellFormed_spine.mpr h₂, h₄⟩⟩
  | flat xs ys hx hy _ =>
    intro e he
    exact ⟨(wellFormed_flat hx).mp ha _ (List.of_mem_zip he).1,
      (wellFormed_flat hy).mp hb _ (List.of_mem_zip he).2⟩

/-! ## The worklist matcher -/

/-- How the matcher sees an instantiated term: `kind == ATOM_VAR`, then
`petta_semantics_is_cons_constraint`, then the flat expressions. -/
inductive Shape
  | var (x : ℕ)
  | sym (s : ℕ)
  | tag
  | cell (h t : Tm)
  | flat (xs : List Tm)

namespace Tm

def shape : Tm → Shape
  | var x => .var x
  | sym s => .sym s
  | tag => .tag
  | cell h t => .cell h t
  | expr xs => .flat xs

theorem shape_var (x : ℕ) : (var x).shape = .var x := rfl

theorem shape_sym (s : ℕ) : (sym s).shape = .sym s := rfl

theorem shape_tag : tag.shape = .tag := rfl

theorem shape_cell (h t : Tm) : (cell h t).shape = .cell h t := rfl

theorem shape_expr {xs : List Tm} (hc : ¬ IsCell (expr xs)) : (expr xs).shape = .flat xs :=
  shape.eq_5 xs fun h t e => hc ⟨h, t, by rw [e]; rfl⟩

end Tm

/-- The outcome of one step on an instantiated pair. -/
inductive Step
  | fail
  | split (pairs : List (Tm × Tm))
  | bind (x : ℕ) (t : Tm)

/-- One step of `petta_semantics_match_cons_constraint`: a variable is bound
after the loop check; two cells, a cell and a nonempty flat list, or two flat
lists of one length are decomposed; two symbols are compared; anything else
fails. -/
def step (a b : Tm) : Step :=
  match a.shape, b.shape with
  | .var x, .var y => if x = y then .split [] else .bind x (.var y)
  | .var x, _ => if b.occurs x then .fail else .bind x b
  | _, .var y => if a.occurs y then .fail else .bind y a
  | .cell h t, .cell h' t' => .split [(h, h'), (t, t')]
  | .cell h t, .flat (y :: ys) => .split [(h, y), (t, spine ys)]
  | .flat (x :: xs), .cell h t => .split [(x, h), (spine xs, t)]
  | .flat xs, .flat ys => if xs.length = ys.length then .split (xs.zip ys) else .fail
  | .sym s, .sym s' => if s = s' then .split [] else .fail
  | _, _ => .fail

/-- `x` occurs in a reference term. -/
inductive PT.Occurs (x : ℕ) : PT → Prop
  | var : Occurs x (.var x)
  | head {h t : PT} : Occurs x h → Occurs x (.cons h t)
  | tail {h t : PT} : Occurs x t → Occurs x (.cons h t)

def PT.size : PT → ℕ
  | cons h t => h.size + t.size + 1
  | _ => 0

theorem PT.size_lt_of_occurs {x : ℕ} {p : PT} (θ : ℕ → PT) (hp : Occurs x p) :
    p = .var x ∨ (θ x).size < (p.subst θ).size := by
  induction hp with
  | var => exact .inl rfl
  | head _ ih | tail _ ih =>
      refine .inr ?_
      rcases ih with rfl | ih <;> simp only [subst, size] at * <;> omega

/-- No substitution equates a variable with a term that properly contains it. -/
theorem PT.subst_ne_of_occurs {x : ℕ} {p : PT} (θ : ℕ → PT) (hp : Occurs x p)
    (hne : p ≠ .var x) : θ x ≠ p.subst θ := fun e =>
  Nat.ne_of_lt ((size_lt_of_occurs θ hp).resolve_left hne) (congrArg size e)

/-- A variable of a term is a variable of its reading. -/
theorem Tm.occurs_denote {x : ℕ} :
    ∀ {t : Tm} {q : PT}, t.denote = some q → t.occurs x = true → q.Occurs x := by
  intro t
  induction t using Tm.induction with
  | sym => intro _ _ h; cases h
  | var v => intro q hq h; cases hq; cases beq_iff_eq.mp h; exact .var
  | tag => intro _ hq; cases hq
  | expr xs ih =>
    intro q hq h
    change occursList x xs = true at h
    by_cases hc : IsCell (expr xs)
    · obtain ⟨a, b, e⟩ := hc
      cases e
      obtain ⟨pa, pb, ha, hb, rfl⟩ := PT.map₂_cons_eq_some hq
      simp only [occursList, occurs, Bool.false_or, Bool.or_false, Bool.or_eq_true] at h
      rcases h with h | h
      exacts [.head (ih a (by simp) ha h), .tail (ih b (by simp) hb h)]
    · rw [denote_expr hc] at hq
      clear hc
      induction xs generalizing q with
      | nil => cases h
      | cons y ys ihy =>
        obtain ⟨py, pys, hy, hys, rfl⟩ := PT.map₂_cons_eq_some hq
        simp only [occursList, Bool.or_eq_true] at h
        rcases h with h | h
        exacts [.head (ih y (List.mem_cons_self ..) hy h),
          .tail (ihy (fun z hz => ih z (List.mem_cons_of_mem _ hz)) hys h)]

/-- The failures of the matcher. -/
inductive Clash : Tm → Tm → Prop
  | loop {x : ℕ} {t : Tm} : t.occurs x = true → t ≠ .var x → Clash (.var x) t
  | tag {b : Tm} : Clash .tag b
  | symSym {s s' : ℕ} : s ≠ s' → Clash (.sym s) (.sym s')
  | symExpr {s : ℕ} {xs : List Tm} : Clash (.sym s) (.expr xs)
  | cellNil {h t : Tm} : Clash (.cell h t) (.expr [])
  | length {xs ys : List Tm} : ¬ IsCell (.expr xs) → ¬ IsCell (.expr ys) →
      xs.length ≠ ys.length → Clash (.expr xs) (.expr ys)
  | swap {a b : Tm} : Clash b a → Clash a b

/-- A clash has no unifier. -/
theorem Clash.not_unifies {a b : Tm} (hc : Clash a b) (θ : ℕ → PT) : ¬ Unifies θ a b := by
  induction hc with
  | loop hocc hne =>
    intro hu
    obtain ⟨q, hq, hx⟩ := unifies_var.mp hu
    exact PT.subst_ne_of_occurs θ (occurs_denote hq hocc)
      (fun e => hne (eq_var_of_denote (e ▸ hq))) hx
  | tag => exact fun ⟨_, _, hp, _⟩ => nomatch hp
  | symSym hne => rintro ⟨_, _, ⟨⟩, ⟨⟩, e⟩; exact hne (PT.atom.inj e)
  | symExpr =>
    rintro ⟨_, q, ⟨⟩, hq, e⟩
    rcases denote_expr_eq_some hq with rfl | ⟨_, _, rfl⟩ <;> cases e
  | cellNil => exact not_unifies_cell_nil θ _ _
  | length hx hy hl => exact fun hu => hl ((unifies_flat_flat θ hx hy).mp hu).length_eq
  | swap _ ih => exact fun hu => ih (unifies_comm.mp hu)

/-- The rules of one step. -/
inductive StepRel : Tm → Tm → Step → Prop
  | split {a b : Tm} {ps : List (Tm × Tm)} : Split a b ps → StepRel a b (.split ps)
  | bind {a b : Tm} {x : ℕ} {t : Tm} : t.occurs x = false →
      (a = .var x ∧ b = t ∨ b = .var x ∧ a = t) → StepRel a b (.bind x t)
  | fail {a b : Tm} : Clash a b → StepRel a b .fail

/-- The matcher's step follows the rules. -/
theorem step_rel (a b : Tm) : StepRel a b (step a b) := by
  rcases view a with ⟨x, rfl⟩ | ⟨s, rfl⟩ | rfl | ⟨h, t, rfl⟩ | ⟨_ | ⟨x, xs⟩, rfl, hx⟩ <;>
  rcases view b with ⟨y, rfl⟩ | ⟨s', rfl⟩ | rfl | ⟨h', t', rfl⟩ | ⟨_ | ⟨y, ys⟩, rfl, hy⟩ <;>
  simp only [step, shape_var, shape_sym, shape_tag, shape_cell, shape_expr,
    not_false_eq_true, ↓reduceIte, *] <;>
  (try split) <;> (try subst_vars) <;>
  first
    | exact .split (by constructor <;> first | assumption | rfl)
    | exact .bind (beq_eq_false_iff_ne.mpr (Ne.symm ‹_›)) (.inl ⟨rfl, rfl⟩)
    | exact .bind (Bool.eq_false_iff.mpr ‹_›) (.inl ⟨rfl, rfl⟩)
    | exact .bind (Bool.eq_false_iff.mpr ‹_›) (.inr ⟨rfl, rfl⟩)
    | exact .fail (.loop ‹_› (by intro e; cases e))
    | exact .fail (.swap (.loop ‹_› (by intro e; cases e)))
    | exact .fail .tag
    | exact .fail (.swap .tag)
    | exact .fail .symExpr
    | exact .fail (.swap .symExpr)
    | exact .fail .cellNil
    | exact .fail (.swap .cellNil)
    | exact .fail (.symSym ‹_›)
    | exact .fail (.length ‹_› ‹_› ‹_›)

/-- The pending pairs, instantiated by the binding `x ↦ t`. -/
def bindPairs (x : ℕ) (t : Tm) (E : List (Tm × Tm)) : List (Tm × Tm) :=
  E.map fun e => (e.1.subst (Function.update var x t), e.2.subst (Function.update var x t))

/-- The outcome of the matcher: a solution, a clash, or exhausted fuel. -/
inductive Outcome
  | solved (σ : ℕ → Tm)
  | clash
  | outOfFuel

/-- The worklist matcher.  CeTTa instantiates each popped pair by the bindings
made so far (`bindings_apply_if_vars`); here each binding instantiates the
pending pairs when it is made and is composed into the answer.  The fuel
bounds the number of steps. -/
def solve : ℕ → List (Tm × Tm) → Outcome
  | _, [] => .solved var
  | 0, _ :: _ => .outOfFuel
  | n + 1, (a, b) :: rest =>
    match step a b with
    | .fail => .clash
    | .split ps => solve n (ps ++ rest)
    | .bind x t =>
      match solve n (bindPairs x t rest) with
      | .solved σ => .solved fun w => (Function.update var x t w).subst σ
      | o => o

/-- A binding that passes the loop check leaves the reading of its term fixed,
so composing any substitution with it solves the binding. -/
theorem unifies_bind {x : ℕ} {t : Tm} {pt : PT} (hocc : t.occurs x = false)
    (ht : t.denote = some pt) (θ : ℕ → PT) :
    Unifies (fun w => (Function.update PT.var x pt w).subst θ) (var x) t := by
  have fixed : pt.subst (Function.update PT.var x pt) = pt := by
    have := denote_subst (represents_update (x := x) ht) t
    rw [subst_update_of_not_occurs t hocc, ht] at this
    exact (Option.some.inj this).symm
  refine unifies_var.mpr ⟨pt, ht, ?_⟩
  show (Function.update PT.var x pt x).subst θ = _
  rw [← PT.subst_subst, fixed, Function.update_self]

/-- Soundness: a solution of a well-formed worklist represents a reference
substitution that unifies the readings of every pair. -/
theorem solve_sound (n : ℕ) : ∀ (E : List (Tm × Tm)) (σ : ℕ → Tm), solve n E = .solved σ →
    (∀ e ∈ E, WellFormed e.1 ∧ WellFormed e.2) →
    ∃ θ, Represents σ θ ∧ ∀ e ∈ E, Unifies θ e.1 e.2 := by
  induction n with
  | zero =>
    rintro (_ | _) σ h _
    · cases h
      exact ⟨PT.var, fun _ => rfl, fun _ h => nomatch h⟩
    · cases h
  | succ n ih =>
    rintro (_ | ⟨⟨a, b⟩, rest⟩) σ h hwf
    · cases h
      exact ⟨PT.var, fun _ => rfl, fun _ h => nomatch h⟩
    have hab := hwf _ (List.mem_cons_self ..)
    have hrest := fun e he => hwf e (List.mem_cons_of_mem _ he)
    simp only [solve] at h
    generalize hs : step a b = s at h
    have hr := step_rel a b
    rw [hs] at hr
    cases hr with
    | split hsp =>
      obtain ⟨θ, hθ, hall⟩ := ih _ σ h fun e he =>
        (List.mem_append.mp he).elim (hsp.wellFormed hab.1 hab.2 e) (hrest e)
      exact ⟨θ, hθ, List.forall_mem_cons.mpr ⟨(hsp.unifies_iff θ).mpr fun e he =>
        hall e (List.mem_append_left _ he), fun e he => hall e (List.mem_append_right _ he)⟩⟩
    | @bind x t hocc hor =>
      obtain ⟨pt, hpt⟩ : WellFormed t := by
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [hab.2, hab.1]
      have hρ := represents_update (x := x) hpt
      cases hso : solve n (bindPairs x t rest) with
      | solved σ' =>
        simp only [hso, Outcome.solved.injEq] at h
        subst h
        obtain ⟨θ', hθ', hall⟩ := ih _ σ' hso fun e' he' => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
          obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hrest e he
          exact ⟨⟨_, by rw [denote_subst hρ, hp]; rfl⟩, ⟨_, by rw [denote_subst hρ, hq]; rfl⟩⟩
        refine ⟨fun w => (Function.update PT.var x pt w).subst θ', fun w => ?_,
          List.forall_mem_cons.mpr ⟨?_, fun e he => ?_⟩⟩
        · rw [denote_subst hθ', hρ w]
          rfl
        · have := unifies_bind hocc hpt θ'
          rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          exacts [this, unifies_comm.mp this]
        · exact (unifies_subst hρ θ' e.1 e.2).mp (hall _ (List.mem_map_of_mem he))
      | clash | outOfFuel => simp only [hso, reduceCtorEq] at h
    | fail => cases h

/-- Soundness for one pair, in terms of the C substitution: both instances
read, and read alike. -/
theorem solve_sound_pair {n : ℕ} {a b : Tm} {σ : ℕ → Tm} (h : solve n [(a, b)] = .solved σ)
    (ha : WellFormed a) (hb : WellFormed b) :
    ∃ p, (a.subst σ).denote = some p ∧ (b.subst σ).denote = some p := by
  obtain ⟨θ, hθ, hall⟩ := solve_sound n _ σ h fun e he => by
    rw [List.mem_singleton.mp he]
    exact ⟨ha, hb⟩
  obtain ⟨p, q, hp, hq, e⟩ := hall _ (List.mem_singleton_self _)
  refine ⟨p.subst θ, ?_, ?_⟩
  · rw [denote_subst hθ, hp]
    rfl
  · rw [denote_subst hθ, hq]
    exact congrArg some e.symm

/-- A clash is genuine: no substitution unifies the readings of the worklist. -/
theorem solve_clash (n : ℕ) : ∀ E : List (Tm × Tm), solve n E = .clash →
    ∀ θ, ¬ ∀ e ∈ E, Unifies θ e.1 e.2 := by
  induction n with
  | zero => rintro (_ | _) h <;> cases h
  | succ n ih =>
    rintro (_ | ⟨⟨a, b⟩, rest⟩) h θ hθ
    · cases h
    have hab := hθ _ (List.mem_cons_self ..)
    have hrest := fun e he => hθ e (List.mem_cons_of_mem _ he)
    simp only [solve] at h
    generalize hs : step a b = s at h
    have hr := step_rel a b
    rw [hs] at hr
    cases hr with
    | split hsp =>
      exact ih _ h θ fun e he =>
        (List.mem_append.mp he).elim ((hsp.unifies_iff θ).mp hab e) (hrest e)
    | @bind x t hocc hor =>
      have hxt : Unifies θ (var x) t := by
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [hab, unifies_comm.mp hab]
      obtain ⟨pt, hpt, hx⟩ := unifies_var.mp hxt
      have fixes : (fun w => (Function.update PT.var x pt w).subst θ) = θ := by
        funext w
        rw [Function.update_apply]
        split_ifs with hw
        exacts [hw ▸ hx.symm, rfl]
      cases hso : solve n (bindPairs x t rest) with
      | clash =>
        refine ih _ hso θ fun e' he' => ?_
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
        have hu := hrest e he
        rw [← fixes] at hu
        exact (unifies_subst (represents_update hpt) θ e.1 e.2).mpr hu
      | solved | outOfFuel => simp only [hso, reduceCtorEq] at h
    | fail hc => exact hc.not_unifies θ hab

/-! ## Examples -/

namespace Examples

/-- The flat pattern `($0 $1 $2)` against the cell of `[1, 2, 3]`: the matcher
binds `$0 $1 $2` to `1 2 3`. -/
theorem pattern_against_cell :
    ∃ σ, solve 10 [(pattern3, list123)] = .solved σ ∧
      σ 0 = sym 1 ∧ σ 1 = sym 2 ∧ σ 2 = sym 3 :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- The cell of `[1, 2, 3]` against the flat list `(1 2 3)`. -/
theorem cell_against_literal :
    (∃ σ, solve 10 [(list123, expr [sym 1, sym 2, sym 3])] = .solved σ) ∧
      ∀ θ, Unifies θ list123 (expr [sym 1, sym 2, sym 3]) :=
  ⟨⟨_, rfl⟩, fun _ => ⟨_, _, rfl, rfl, rfl⟩⟩

/-- A cell with a variable tail against a longer flat list: the tail is bound
to the spine of the suffix, which reads as the suffix. -/
theorem open_tail_binds_suffix :
    ∃ σ, solve 10 [(cell (sym 1) (var 0), expr [sym 1, sym 2, sym 3])] = .solved σ ∧
      σ 0 = spine [sym 2, sym 3] ∧ (σ 0).denote = (expr [sym 2, sym 3]).denote :=
  ⟨_, rfl, rfl, rfl⟩

/-- Two flat lists whose elements are a cell and a flat list of one reading. -/
theorem cell_inside_flat_list :
    ∃ σ, solve 10 [(expr [list12, var 0], expr [expr [sym 1, sym 2], sym 3])] = .solved σ ∧
      σ 0 = sym 3 :=
  ⟨_, rfl, rfl⟩

/-- The cell of `[1, 2, 3]` flattens to the flat list, which the three-field
pattern then meets structurally, binding `$0` to `1`. -/
theorem closed_chain_flattens :
    list123.flat = expr [sym 1, sym 2, sym 3] ∧
      (Closed list123 ∧ TagFree list123.flat) := by
  have hc : Closed list123 :=
    .cell (.sym 1) (.flat _ (by decide) fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact .sym _)
  exact ⟨rfl, hc, hc.tagFree_flat⟩

/-- A chain ending in a variable is a partial list: it is not closed, and it
keeps its cell when flattened. -/
theorem open_chain_keeps_its_cell :
    ¬ Closed (cell (sym 1) (var 0)) ∧ (cell (sym 1) (var 0)).flat = cell (sym 1) (var 0) := by
  refine ⟨fun h => ?_, rfl⟩
  cases h with
  | flat _ hc _ => exact hc ⟨_, _, rfl⟩

/-- A `cons` spelled in data, here as symbol 7, is an ordinary three-element
list: tag-free, and left as it is. -/
theorem spelled_cons_is_data :
    TagFree (expr [sym 7, sym 1, sym 2]) ∧
      (expr [sym 7, sym 1, sym 2]).flat = expr [sym 7, sym 1, sym 2] := by
  refine ⟨.expr _ fun x hx => ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact .sym _

end Examples

namespace Controls

/-- A cell against the empty expression: a clash, and no unifier. -/
theorem cell_against_empty :
    solve 10 [(list123, expr [])] = .clash ∧ ∀ θ, ¬ Unifies θ list123 (expr []) :=
  ⟨rfl, fun θ => not_unifies_cell_nil θ _ _⟩

/-- Cells of different lengths, `[1]` and `[1, 2, 3]`: a clash, and no unifier. -/
theorem cells_of_different_lengths :
    solve 10 [(cell (sym 1) (expr []), list123)] = .clash ∧
      ∀ θ, ¬ Unifies θ (cell (sym 1) (expr [])) list123 :=
  ⟨rfl, fun θ h => solve_clash 10 [(cell (sym 1) (expr []), list123)] rfl θ fun e he => by
    rw [List.mem_singleton.mp he]
    exact h⟩

/-- The loop check: `$0` against `[1 | $0]` clashes, and has no unifier. -/
theorem loop :
    solve 10 [(var 0, cell (sym 1) (var 0))] = .clash ∧
      ∀ θ, ¬ Unifies θ (var 0) (cell (sym 1) (var 0)) :=
  ⟨rfl, fun θ h => solve_clash 10 [(var 0, cell (sym 1) (var 0))] rfl θ fun e he => by
    rw [List.mem_singleton.mp he]
    exact h⟩

/-- Exhausted fuel is not a clash. -/
theorem fuel_is_not_a_clash : solve 1 [(pattern3, list123)] = .outOfFuel := rfl

/-- A substitution that plants a bare tag manufactures a cell: the instance of
the flat pattern reads as `[1, 2, 3]`, although the image of `$0` has no
reading.  Reading commutes only with represented substitutions. -/
theorem planted_tag_makes_a_cell :
    let σ : ℕ → Tm := fun v => [tag, sym 1, expr [sym 2, sym 3]].getD v (var v)
    (σ 0).denote = none ∧ (pattern3.subst σ).denote = list123.denote :=
  ⟨rfl, rfl⟩

/-- (b) with the flat rest needs the rest to be no cell: in the ill-formed
flat list `(0 tag 1 ())` the heads unify and the tail unifies with the rest
`(tag 1 ())`, which is a cell, yet the lists do not unify. -/
theorem flat_rest_must_not_be_a_cell (θ : ℕ → PT) :
    ¬ Unifies θ (cell (sym 0) (cell (sym 1) (expr []))) (expr [sym 0, tag, sym 1, expr []]) ∧
      Unifies θ (sym 0) (sym 0) ∧
      Unifies θ (cell (sym 1) (expr [])) (expr [tag, sym 1, expr []]) :=
  ⟨fun ⟨_, _, _, hq, _⟩ => (nomatch hq), ⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, rfl⟩⟩

end Controls

end Mettapedia.Machines.Cursor.ListCells
