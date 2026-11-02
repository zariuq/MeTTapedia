import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Thin
import Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

/-!
# Thinnings act on binding trees

The terms of the guarded rewriting calculus are binding trees, `SignatureIndexedABT.Term Head`: a leaf `idx n`
is the variable bound `n` binders out, and each field of a node sits under the number of binders
its head declares. A thinning `θ` **renames** a tree (`rename θ t`): free variable `j` becomes
`sel θ j`, and under a field's `d` binders the thinning keeps those `d` (`keepN d θ`).

Example: `rename [false, true] (idx 0) = idx 1`: the variable is moved past a new innermost one.

* **Renaming is a functor** from thinnings to trees: `rename [] t = t` (`rename_nil`) and
  `rename φ (rename θ t) = rename (comp θ φ) t` (`rename_comp`); it loses nothing
  (`rename_injective`).
* **Shifts are thinnings**: `Term.lift c a t = rename (keepN c (dropN a [])) t` (`lift_eq_rename`);
  a shift by `k` at the root is the thinning that skips `k` innermost variables.
* `freeAt t i`: variable `i` is free in `t`. Renaming moves the free variables along the thinning
  (`freeAt_rename`).
* A tree is **relevant** at `m` when its free variables are exactly `0, …, m - 1` (`Relevant`):
  every variable of its scope is used. A relevant tree renamed by `θ` has exactly the kept
  positions of `θ` free (`freeAt_rename_relevant`). So **a trimmed thinning and a relevant tree
  are determined by the tree they give** (`rename_trimmed_inj`), and so are an exact-length
  thinning and a relevant tree (`rename_exact_inj`). This is the canonicity behind co-de-Bruijn
  terms and pointer equality.
* **Opening an unused variable only erases it from the thinning** (`instantiateAt_rename_unused`):
  no part of the tree is visited.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

variable {Head : Type}

/-! ## Renaming -/

mutual

/-- **Rename a tree along a thinning**: free variable `j` becomes `sel θ j`. -/
def rename : Thin → Term Head → Term Head
  | θ, .idx j => .idx (sel θ j)
  | θ, .node h fs => .node h (renameFields θ fs)

/-- Rename each field under its binders, which the thinning keeps. -/
def renameFields : Thin → Fields Head → Fields Head
  | _, .nil => .nil
  | θ, .cons d t rest => .cons d (rename (keepN d θ) t) (renameFields θ rest)

end

@[simp] theorem rename_idx (θ : Thin) (j : ℕ) : rename θ (.idx j : Term Head) = .idx (sel θ j) := by
  simp [rename]

@[simp] theorem rename_node (θ : Thin) (h : Head) (fs : Fields Head) :
    rename θ (.node h fs) = .node h (renameFields θ fs) := by
  simp [rename]

@[simp] theorem renameFields_nil (θ : Thin) : renameFields θ (.nil : Fields Head) = .nil := by
  simp [renameFields]

@[simp] theorem renameFields_cons (θ : Thin) (d : ℕ) (t : Term Head) (rest : Fields Head) :
    renameFields θ (.cons d t rest) = .cons d (rename (keepN d θ) t) (renameFields θ rest) := by
  simp [renameFields]

mutual

/-- **Renaming composes**: renaming by `θ` then by `φ` is renaming by `comp θ φ`. -/
theorem rename_comp (θ φ : Thin) (t : Term Head) : rename φ (rename θ t) = rename (comp θ φ) t := by
  cases t with
  | idx j => simp [sel_comp]
  | node h fs => simp [renameFields_comp θ φ fs]

theorem renameFields_comp (θ φ : Thin) (fs : Fields Head) :
    renameFields φ (renameFields θ fs) = renameFields (comp θ φ) fs := by
  cases fs with
  | nil => simp
  | cons d t rest =>
      simp [rename_comp (keepN d θ) (keepN d φ) t, comp_keepN, renameFields_comp θ φ rest]

end

mutual

/-- A thinning that moves no variable renames nothing. -/
theorem rename_of_sel_id {θ : Thin} (id : ∀ j, sel θ j = j) (t : Term Head) : rename θ t = t := by
  cases t with
  | idx j => simp [id]
  | node h fs => simp [renameFields_of_sel_id id fs]

theorem renameFields_of_sel_id {θ : Thin} (id : ∀ j, sel θ j = j) (fs : Fields Head) :
    renameFields θ fs = fs := by
  cases fs with
  | nil => simp
  | cons d t rest =>
      have id' : ∀ j, sel (keepN d θ) j = j := by
        intro j
        rw [sel_keepN]
        split_ifs with h
        · rfl
        · rw [id]; omega
      simp [rename_of_sel_id id' t, renameFields_of_sel_id id rest]

end

/-- **The empty thinning renames nothing.** -/
@[simp] theorem rename_nil (t : Term Head) : rename [] t = t := rename_of_sel_id sel_nil t

mutual

/-- **Renaming loses nothing.** -/
theorem rename_injective (θ : Thin) : ∀ s t : Term Head, rename θ s = rename θ t → s = t
  | .idx a, .idx b, h => by simpa using sel_injective θ (by simpa using h)
  | .idx _, .node _ _, h => by simp at h
  | .node _ _, .idx _, h => by simp at h
  | .node h₁ f₁, .node h₂ f₂, h => by
      simp only [rename_node, Term.node.injEq] at h
      rw [h.1, renameFields_injective θ f₁ f₂ h.2]

theorem renameFields_injective (θ : Thin) :
    ∀ f g : Fields Head, renameFields θ f = renameFields θ g → f = g
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _ _, h => by simp at h
  | .cons _ _ _, .nil, h => by simp at h
  | .cons d₁ t₁ r₁, .cons d₂ t₂ r₂, h => by
      simp only [renameFields_cons, Fields.cons.injEq] at h
      obtain ⟨hd, ht, hr⟩ := h
      subst hd
      rw [rename_injective (keepN d₁ θ) t₁ t₂ ht, renameFields_injective θ r₁ r₂ hr]

end

/-! ## Shifts are thinnings -/

mutual

/-- **A shift is a renaming**: shifting by `a` past `c` keeps the `c` innermost variables and
skips `a` new ones. -/
theorem lift_eq_rename (c a : ℕ) (t : Term Head) :
    Term.lift c a t = rename (keepN c (dropN a [])) t := by
  cases t with
  | idx n =>
      simp only [Term.lift, rename_idx, sel_keepN, sel_dropN, sel_nil]
      split_ifs with h
      · rfl
      · congr 1; omega
  | node h fs =>
      simp only [Term.lift, rename_node]
      rw [fields_lift_eq_rename c a fs]

theorem fields_lift_eq_rename (c a : ℕ) (fs : Fields Head) :
    Term.Fields.lift c a fs = renameFields (keepN c (dropN a [])) fs := by
  cases fs with
  | nil => simp [Term.Fields.lift]
  | cons d t rest =>
      simp only [Term.Fields.lift, renameFields_cons]
      rw [lift_eq_rename (c + d) a t, fields_lift_eq_rename c a rest, keepN_add, Nat.add_comm c d]

end

/-- A shift at the root by `k` is the thinning that skips the `k` innermost variables. -/
theorem lift_zero_eq_rename (k : ℕ) (t : Term Head) : Term.lift 0 k t = rename (dropN k []) t := by
  rw [lift_eq_rename]; simp [keepN]

/-! ## Free variables -/

mutual

/-- `freeAt t i`: variable `i` is free in `t` (seen from the root of `t`). -/
def freeAt : Term Head → ℕ → Bool
  | .idx n, i => decide (n = i)
  | .node _ fields, i => fieldsFreeAt fields i

/-- A field under `d` binders sees the root's variable `i` as its own variable `i + d`. -/
def fieldsFreeAt : Fields Head → ℕ → Bool
  | .nil, _ => false
  | .cons d t rest, i => freeAt t (i + d) || fieldsFreeAt rest i

end

@[simp] theorem freeAt_idx (n i : ℕ) : freeAt (.idx n : Term Head) i = decide (n = i) := by
  simp [freeAt]

@[simp] theorem freeAt_node (h : Head) (fs : Fields Head) (i : ℕ) :
    freeAt (.node h fs) i = fieldsFreeAt fs i := by
  simp [freeAt]

@[simp] theorem fieldsFreeAt_nil (i : ℕ) : fieldsFreeAt (.nil : Fields Head) i = false := by
  simp [fieldsFreeAt]

@[simp] theorem fieldsFreeAt_cons (d : ℕ) (t : Term Head) (rest : Fields Head) (i : ℕ) :
    fieldsFreeAt (.cons d t rest) i = (freeAt t (i + d) || fieldsFreeAt rest i) := by
  simp [fieldsFreeAt]

mutual

/-- **Renaming moves the free variables along the thinning.** -/
theorem freeAt_rename (θ : Thin) (t : Term Head) (i : ℕ) :
    freeAt (rename θ t) i = true ↔ ∃ j, freeAt t j = true ∧ sel θ j = i := by
  cases t with
  | idx n => simp
  | node h fs => simpa using fieldsFreeAt_rename θ fs i

theorem fieldsFreeAt_rename (θ : Thin) (fs : Fields Head) (i : ℕ) :
    fieldsFreeAt (renameFields θ fs) i = true ↔ ∃ j, fieldsFreeAt fs j = true ∧ sel θ j = i := by
  cases fs with
  | nil => simp
  | cons d t rest =>
      simp only [renameFields_cons, fieldsFreeAt_cons, Bool.or_eq_true]
      rw [freeAt_rename (keepN d θ) t (i + d), fieldsFreeAt_rename θ rest i]
      constructor
      · rintro (⟨j, fj, sj⟩ | ⟨j, fj, sj⟩)
        · have big : d ≤ j := by
            by_contra small
            rw [sel_keepN_lt θ (by omega)] at sj
            omega
          obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
          rw [sel_keepN_add] at sj
          exact ⟨j', Or.inl (by rwa [Nat.add_comm j' d]), by omega⟩
        · exact ⟨j, Or.inr fj, sj⟩
      · rintro ⟨j, fj | fj, sj⟩
        · exact Or.inl ⟨d + j, by rwa [Nat.add_comm d j], by rw [sel_keepN_add, sj]; omega⟩
        · exact Or.inr ⟨j, fj, sj⟩

end

mutual

/-- **Renaming depends only on the free variables**: thinnings that agree on them rename alike. -/
theorem rename_congr {θ θ' : Thin} (t : Term Head) (same : ∀ j, freeAt t j = true → sel θ j = sel θ' j) :
    rename θ t = rename θ' t := by
  cases t with
  | idx n => simpa using same n (by simp)
  | node h fs => simpa using renameFields_congr fs (by simpa using same)

theorem renameFields_congr {θ θ' : Thin} (fs : Fields Head)
    (same : ∀ j, fieldsFreeAt fs j = true → sel θ j = sel θ' j) :
    renameFields θ fs = renameFields θ' fs := by
  cases fs with
  | nil => simp
  | cons d t rest =>
      simp only [renameFields_cons]
      rw [rename_congr t (fun j fj => ?_), renameFields_congr rest (fun j fj => same j (by simp [fj]))]
      by_cases small : j < d
      · rw [sel_keepN_lt θ small, sel_keepN_lt θ' small]
      · obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
        rw [sel_keepN_add, sel_keepN_add, same j' (by simp [Nat.add_comm j' d, fj])]

end

/-- A tree is **closed** when no variable is free in it. -/
def Closed (t : Term Head) : Prop := ∀ i, freeAt t i = false

/-- A closed tree is not changed by renaming. -/
theorem rename_of_closed {t : Term Head} (closed : Closed t) (θ : Thin) : rename θ t = t :=
  (rename_congr (θ' := []) t fun j fj => by rw [closed j] at fj; cases fj).trans (rename_nil t)

/-! ## Relevant trees -/

/-- A tree is **relevant** at `m` when its free variables are exactly `0, …, m - 1`: every
variable of its scope is used. -/
def Relevant (m : ℕ) (t : Term Head) : Prop := ∀ i, freeAt t i = true ↔ i < m

theorem Relevant.closed {t : Term Head} (rel : Relevant 0 t) : Closed t := by
  intro i
  cases h : freeAt t i
  · rfl
  · exact absurd ((rel i).mp h) (Nat.not_lt_zero _)

/-- **A relevant tree, renamed, has exactly the kept positions of the thinning free.** -/
theorem freeAt_rename_relevant {θ : Thin} {t : Term Head} (rel : Relevant (ones θ) t) (i : ℕ) :
    freeAt (rename θ t) i = bit θ i := by
  apply Bool.eq_iff_iff.mpr
  rw [freeAt_rename, bit_iff_exists_sel]
  constructor
  · rintro ⟨j, fj, sj⟩; exact ⟨j, (rel j).mp fj, sj⟩
  · rintro ⟨j, lt, sj⟩; exact ⟨j, (rel j).mpr lt, sj⟩

/-- Thinnings that agree on the first `m` variables rename a tree relevant at `m` alike. -/
theorem rename_congr_relevant {m : ℕ} {θ θ' : Thin} {t : Term Head} (rel : Relevant m t)
    (same : ∀ j < m, sel θ j = sel θ' j) : rename θ t = rename θ' t :=
  rename_congr t fun j fj => same j ((rel j).mp fj)

/-- **Canonicity of trimmed references**: a trimmed thinning and a tree relevant at its kept
count are determined by the tree they give. -/
theorem rename_trimmed_inj {θ θ' : Thin} {s s' : Term Head} (h : trimmed θ = true)
    (h' : trimmed θ' = true) (rel : Relevant (ones θ) s) (rel' : Relevant (ones θ') s')
    (same : rename θ s = rename θ' s') : θ = θ' ∧ s = s' := by
  have bits : ∀ i, bit θ i = bit θ' i := fun i => by
    rw [← freeAt_rename_relevant rel, ← freeAt_rename_relevant rel', same]
  have eq := trimmed_ext h h' bits
  subst eq
  exact ⟨rfl, rename_injective θ s s' same⟩

/-- **Canonicity of edges**: an exact-length thinning and a tree relevant at its kept count are
determined, among thinnings of that length, by the tree they give. -/
theorem rename_exact_inj {θ θ' : Thin} {s s' : Term Head} (len : θ.length = θ'.length)
    (rel : Relevant (ones θ) s) (rel' : Relevant (ones θ') s')
    (same : rename θ s = rename θ' s') : θ = θ' ∧ s = s' := by
  have bits : ∀ i, bit θ i = bit θ' i := fun i => by
    rw [← freeAt_rename_relevant rel, ← freeAt_rename_relevant rel', same]
  have eq := eq_of_bits_of_length len bits
  subst eq
  exact ⟨rfl, rename_injective θ s s' same⟩

/-! ## Opening a binder -/

mutual

/-- Opening a variable that a one-step shift jumped over undoes the shift. -/
theorem instantiateAt_lift_one (d : ℕ) (V t : Term Head) :
    Term.instantiateAt d V (Term.lift d 1 t) = t := by
  cases t with
  | idx n =>
      by_cases h : n < d
      · simp [Term.lift, Term.instantiateAt, h]
      · have h1 : ¬ n + 1 < d := by omega
        have h2 : ¬ n + 1 = d := by omega
        simp [Term.lift, Term.instantiateAt, h, h1, h2]
  | node h fs =>
      simp only [Term.lift, Term.instantiateAt]
      rw [fields_instantiateAt_lift_one d V fs]

theorem fields_instantiateAt_lift_one (d : ℕ) (V : Term Head) (fs : Fields Head) :
    Term.Fields.instantiateAt d V (Term.Fields.lift d 1 fs) = fs := by
  cases fs with
  | nil => rfl
  | cons fd t rest =>
      simp only [Term.Fields.lift, Term.Fields.instantiateAt]
      rw [instantiateAt_lift_one (d + fd) V t, fields_instantiateAt_lift_one d V rest]

end

/-- **Opening an unused variable erases it from the thinning**: if `θ` does not keep position `d`,
then opening variable `d` of `rename θ t` (for `t` relevant) is renaming by `θ` without that
position. Nothing of `t` is visited. -/
theorem instantiateAt_rename_unused {d : ℕ} {θ : Thin} {t : Term Head} (rel : Relevant (ones θ) t)
    (unused : bit θ d = false) (V : Term Head) :
    Term.instantiateAt d V (rename θ t) = rename (erase d θ) t := by
  have split : rename θ t = Term.lift d 1 (rename (erase d θ) t) := by
    rw [lift_eq_rename, rename_comp]
    refine rename_congr_relevant rel fun j lt => ?_
    rw [sel_comp, sel_keepN, sel_dropN, sel_erase unused lt]
    split_ifs with h
    · rfl
    · simp; omega
  rw [split, instantiateAt_lift_one]

/-- Opening the variable a leaf stands for gives the value, shifted past the binders crossed. -/
theorem instantiateAt_rename_var {d : ℕ} {θ : Thin} (at_d : sel θ 0 = d) (V : Term Head) :
    Term.instantiateAt d V (rename θ (.idx 0)) = rename (dropN d []) V := by
  simp [Term.instantiateAt, at_d, lift_zero_eq_rename]

/-! ## Deciding equality of trees -/

mutual

/-- Structural comparison of trees. -/
def termBeq [DecidableEq Head] : Term Head → Term Head → Bool
  | .idx a, .idx b => decide (a = b)
  | .node h fs, .node h' fs' => decide (h = h') && fieldsBeq fs fs'
  | .idx _, .node _ _ => false
  | .node _ _, .idx _ => false

def fieldsBeq [DecidableEq Head] : Fields Head → Fields Head → Bool
  | .nil, .nil => true
  | .cons d t r, .cons d' t' r' => decide (d = d') && termBeq t t' && fieldsBeq r r'
  | .nil, .cons _ _ _ => false
  | .cons _ _ _, .nil => false

end

mutual

theorem termBeq_iff [DecidableEq Head] (s t : Term Head) : termBeq s t = true ↔ s = t := by
  cases s with
  | idx a =>
      cases t with
      | idx b => simp [termBeq]
      | node _ _ => simp [termBeq]
  | node h fs =>
      cases t with
      | idx b => simp [termBeq]
      | node h' fs' =>
          simp only [termBeq, Bool.and_eq_true, decide_eq_true_eq, Term.node.injEq]
          rw [fieldsBeq_iff fs fs']

theorem fieldsBeq_iff [DecidableEq Head] (f g : Fields Head) : fieldsBeq f g = true ↔ f = g := by
  cases f with
  | nil =>
      cases g with
      | nil => simp [fieldsBeq]
      | cons _ _ _ => simp [fieldsBeq]
  | cons d t r =>
      cases g with
      | nil => simp [fieldsBeq]
      | cons d' t' r' =>
          simp only [fieldsBeq, Bool.and_eq_true, decide_eq_true_eq, Fields.cons.injEq]
          rw [termBeq_iff t t', fieldsBeq_iff r r']
          tauto

end

instance instDecidableEqTerm [DecidableEq Head] : DecidableEq (Term Head) :=
  fun s t => decidable_of_iff _ (termBeq_iff s t)

/-! ## Examples -/

namespace RenameControls

/-- One binary head (application) and one binder. -/
inductive H where
  | app
  | lam
  deriving DecidableEq

def app (f x : Term H) : Term H := .node .app (.cons 0 f (.cons 0 x .nil))

def lam (b : Term H) : Term H := .node .lam (.cons 1 b .nil)

/-- Positive: renaming `λ. (0 1)` by `[false, true]` moves its free variable past a new innermost
one, giving `λ. (0 2)`, and keeps the bound variable. -/
theorem rename_example : rename [false, true] (lam (app (.idx 0) (.idx 1))) = lam (app (.idx 0) (.idx 2)) := by
  decide

/-- Positive: `λ. (0 2)` uses its scope's variable `1` but not `0`; `λ. (0 1)` is relevant at `1`. -/
theorem free_example :
    freeAt (lam (app (.idx 0) (.idx 2))) 1 = true ∧ freeAt (lam (app (.idx 0) (.idx 2))) 0 = false := by
  decide

/-- Negative: renaming is not the identity on an open tree. -/
theorem rename_moves : rename [false] (.idx 0 : Term H) ≠ .idx 0 := by decide

end RenameControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
