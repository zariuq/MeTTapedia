import Mettapedia.InformationTheory.RelationStoreVariantKeys
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatching

/-!
# Scoped keys: one key layer for variant keys and contextual matching

The terms of the Prime calculus are binding trees: a leaf `idx j` under `d` binders is bound when
`j < d` and is the free variable `j - d` otherwise.  Binding trees are de Bruijn terms, so
alpha-equivalent terms are equal trees.  Two trees are **variants** (`FVariant`) when each is the
other with its free variables renamed (`frename`).  Example: `(f 0 1)` and `(f 5 3)` are variants;
`(f 0 0)` is not their variant; under one binder, `λ. (g 0 1)` and `λ. (g 0 2)` are variants, and
`λ. (g 0 1)` and `λ. (g 1 0)` are not (the bound variable is not renamed).

* `fenc` writes a tree as a binary term of `RelationStoreVariantKeys`: bound indices become atoms,
  free variables become variables.  It is injective and turns `frename` into renaming
  (`fenc_frename`), so the first-occurrence key of the encoding identifies exactly the variants
  (`skey_eq_iff_variant`).  Keys are equal iff the terms are alpha-equivalent up to the names of
  their free variables.
* A thinning is a renaming of free variables (`rename_eq_frename`), injective, so a thinned tree is
  a variant of the tree (`fvariant_rename`).
* **On the shared store**: the key of a reference is the key of its node (`refKey_eq_nodeKey`),
  whatever the reference's thinning.  So one key per stored node serves every reference to it.
  Contextual matching (`restrictRef`) and weakening keep the key (`refKey_restrictRef`,
  `refKey_weakenRef`).  Keys of references are equal exactly when the trees they stand for are
  variants (`refKey_eq_iff`).
* **Composition** (`canon_pair`): the first-occurrence key of a pair is computed from the keys of
  its two parts and their variable lists.
-/

namespace Mettapedia.InformationTheory.SymmetryKeys.Scoped

open Mettapedia.InformationTheory.RelationStoreVariantKeys
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Thin

variable {Head : Type}

/-- Tokens of the encoding: a head, a bound index, a field's binder count, the end of fields. -/
inductive STok (Head : Type) where
  | head : Head → STok Head
  | bound : ℕ → STok Head
  | depth : ℕ → STok Head
  | nil : STok Head
  deriving DecidableEq

mutual

/-- A binding tree beneath `d` binders as a binary term: bound indices are atoms, free variables
are variables. -/
def fenc (d : ℕ) : Term Head → Tm (STok Head) ℕ
  | .idx j => if j < d then .atom (.bound j) else .var (j - d)
  | .node h fs => .pair (.atom (.head h)) (fencFields d fs)

/-- The fields of a node, each with its binder count. -/
def fencFields (d : ℕ) : Fields Head → Tm (STok Head) ℕ
  | .nil => .atom .nil
  | .cons k t rest => .pair (.pair (.atom (.depth k)) (fenc (d + k) t)) (fencFields d rest)

end

mutual

/-- Rename the free variables of a binding tree beneath `d` binders. -/
def frename (f : ℕ → ℕ) (d : ℕ) : Term Head → Term Head
  | .idx j => if j < d then .idx j else .idx (d + f (j - d))
  | .node h fs => .node h (frenameFields f d fs)

/-- `frename` on each field, beneath its binders. -/
def frenameFields (f : ℕ → ℕ) (d : ℕ) : Fields Head → Fields Head
  | .nil => .nil
  | .cons k t rest => .cons k (frename f (d + k) t) (frenameFields f d rest)

end

mutual

theorem fenc_frename (f : ℕ → ℕ) : ∀ (d : ℕ) (t : Term Head),
    fenc d (frename f d t) = (fenc d t).rename f
  | d, .idx j => by
      by_cases hj : j < d
      · simp [frename, fenc, hj, Tm.rename]
      · have hj' : ¬ d + f (j - d) < d := by omega
        simp [frename, fenc, hj, hj', Tm.rename]
  | d, .node h fs => by
      simp only [frename, fenc, Tm.rename]
      rw [fencFields_frename f d fs]

theorem fencFields_frename (f : ℕ → ℕ) : ∀ (d : ℕ) (fs : Fields Head),
    fencFields d (frenameFields f d fs) = (fencFields d fs).rename f
  | _, .nil => rfl
  | d, .cons k t rest => by
      simp only [frenameFields, fencFields, Tm.rename]
      rw [fenc_frename f (d + k) t, fencFields_frename f d rest]

end

mutual

theorem fenc_inj : ∀ (d : ℕ) (s t : Term Head), fenc d s = fenc d t → s = t
  | d, .idx j, .idx j', e => by
      by_cases hj : j < d <;> by_cases hj' : j' < d <;> simp [fenc, hj, hj'] at e
      · rw [e]
      · have : j = j' := by omega
        rw [this]
  | d, .idx j, .node _ _, e => by
      by_cases hj : j < d <;> simp [fenc, hj] at e
  | d, .node _ _, .idx j, e => by
      by_cases hj : j < d <;> simp [fenc, hj] at e
  | d, .node h fs, .node h' fs', e => by
      simp only [fenc, Tm.pair.injEq, Tm.atom.injEq, STok.head.injEq] at e
      rw [e.1, fencFields_inj d fs fs' e.2]

theorem fencFields_inj : ∀ (d : ℕ) (fs fs' : Fields Head),
    fencFields d fs = fencFields d fs' →
    fs = fs'
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons _ _ _, e => by simp [fencFields] at e
  | _, .cons _ _ _, .nil, e => by simp [fencFields] at e
  | d, .cons k t rest, .cons k' t' rest', e => by
      simp only [fencFields, Tm.pair.injEq, Tm.atom.injEq, STok.depth.injEq] at e
      obtain ⟨⟨hk, ht⟩, hr⟩ := e
      subst hk
      rw [fenc_inj (d + k) t t' ht, fencFields_inj d rest rest' hr]

end

mutual

theorem frename_comp (f g : ℕ → ℕ) : ∀ (d : ℕ) (t : Term Head),
    frename f d (frename g d t) = frename (f ∘ g) d t
  | d, .idx j => by
      by_cases hj : j < d
      · simp [frename, hj]
      · have hj' : ¬ d + g (j - d) < d := by omega
        simp [frename, hj, hj']
  | d, .node h fs => by
      simp only [frename]
      rw [frenameFields_comp f g d fs]

theorem frenameFields_comp (f g : ℕ → ℕ) : ∀ (d : ℕ) (fs : Fields Head),
    frenameFields f d (frenameFields g d fs) = frenameFields (f ∘ g) d fs
  | _, .nil => rfl
  | d, .cons k t rest => by
      simp only [frenameFields]
      rw [frename_comp f g (d + k) t, frenameFields_comp f g d rest]

end

mutual

theorem frename_id : ∀ (d : ℕ) (t : Term Head), frename id d t = t
  | d, .idx j => by
      by_cases hj : j < d
      · simp [frename, hj]
      · simp only [frename, hj, if_false, id_eq]
        congr 1
        omega
  | d, .node h fs => by
      simp only [frename]
      rw [frenameFields_id d fs]

theorem frenameFields_id : ∀ (d : ℕ) (fs : Fields Head), frenameFields id d fs = fs
  | _, .nil => rfl
  | d, .cons k t rest => by
      simp only [frenameFields]
      rw [frename_id (d + k) t, frenameFields_id d rest]

end

mutual

theorem frename_sel (θ : Thin) : ∀ (d : ℕ) (t : Term Head),
    frename (sel θ) d t = rename (keepN d θ) t
  | d, .idx j => by
      rw [rename_idx, sel_keepN]
      by_cases hj : j < d <;> simp [frename, hj]
  | d, .node h fs => by
      simp only [frename, rename_node]
      rw [frenameFields_sel θ d fs]

theorem frenameFields_sel (θ : Thin) : ∀ (d : ℕ) (fs : Fields Head),
    frenameFields (sel θ) d fs = renameFields (keepN d θ) fs
  | _, .nil => rfl
  | d, .cons k t rest => by
      simp only [frenameFields, renameFields_cons]
      rw [frename_sel θ (d + k) t, frenameFields_sel θ d rest, keepN_add, Nat.add_comm]

end

/-- **A thinning renames free variables.** -/
theorem rename_eq_frename (θ : Thin) (t : Term Head) : rename θ t = frename (sel θ) 0 t := by
  rw [frename_sel]
  simp [keepN]

/-- Each tree is the other with its free variables renamed. -/
def FVariant (s t : Term Head) : Prop :=
  (∃ f : ℕ → ℕ, frename f 0 s = t) ∧ ∃ g : ℕ → ℕ, frename g 0 t = s

theorem fvariant_iff_enc {s t : Term Head} :
    FVariant s t ↔ Tm.Variant (fenc 0 s) (fenc 0 t) := by
  constructor
  · rintro ⟨⟨f, hf⟩, g, hg⟩
    exact ⟨⟨f, by rw [← fenc_frename, hf]⟩, g, by rw [← fenc_frename, hg]⟩
  · rintro ⟨⟨f, hf⟩, g, hg⟩
    exact ⟨⟨f, fenc_inj 0 _ _ (by rw [fenc_frename, hf])⟩, g,
      fenc_inj 0 _ _ (by rw [fenc_frename, hg])⟩

theorem fvariant_symm {s t : Term Head} (h : FVariant s t) : FVariant t s := ⟨h.2, h.1⟩

theorem sel_injective (θ : Thin) : Function.Injective (sel θ) :=
  StrictMono.injective fun _ _ h => sel_lt_sel θ h

/-- **A thinned tree is a variant of the tree.** -/
theorem fvariant_rename (θ : Thin) (t : Term Head) : FVariant t (rename θ t) := by
  refine ⟨⟨sel θ, (rename_eq_frename θ t).symm⟩, Function.invFun (sel θ), ?_⟩
  rw [rename_eq_frename, frename_comp]
  have hinv : Function.invFun (sel θ) ∘ sel θ = id :=
    funext (Function.leftInverse_invFun (sel_injective θ))
  rw [hinv, frename_id]

/-- The key of a binding tree: the first-occurrence key of its encoding. -/
def skey (t : Term Head) : Tm (STok Head) ℕ := canon (fenc 0 t)

/-- **Keys are equal exactly on variants**: alpha-equivalent trees up to the names of their free
variables. -/
theorem skey_eq_iff_variant {s t : Term Head} : skey s = skey t ↔ FVariant s t :=
  canon_eq_iff_variant.trans fvariant_iff_enc.symm

/-! ### The shared store -/

/-- The key of a reference: the key of the tree it stands for. -/
def refKey (St : Store Head) (r : Ref) : Tm (STok Head) ℕ := skey (unfold St r)

/-- The key of a stored node. -/
def nodeKey (St : Store Head) (i : ℕ) : Tm (STok Head) ℕ := skey (nodeTree St i)

/-- **One key per stored node**: a reference has the key of its node, whatever its thinning. -/
theorem refKey_eq_nodeKey (St : Store Head) (r : Ref) : refKey St r = nodeKey St r.id :=
  skey_eq_iff_variant.mpr (fvariant_symm (by rw [unfold_eq]; exact fvariant_rename r.thin _))

/-- **Keys of references are equal exactly when the trees they stand for are variants.** -/
theorem refKey_eq_iff (St : Store Head) (r r' : Ref) :
    refKey St r = refKey St r' ↔ FVariant (unfold St r) (unfold St r') :=
  skey_eq_iff_variant

/-- **Contextual matching keeps the key**: the assignment of a contextual hole has the key of the
source reference. -/
theorem refKey_restrictRef (St : Store Head) {allowed : Thin} {source body : Ref}
    (h : ContextualMatching.restrictRef allowed source = some body) :
    refKey St body = refKey St source := by
  unfold ContextualMatching.restrictRef at h
  split at h
  · rw [refKey_eq_nodeKey, refKey_eq_nodeKey, ← Option.some.inj h]
    rfl
  · cases h

/-- Weakening keeps the key. -/
theorem refKey_weakenRef (St : Store Head) (ρ : Thin) (r : Ref) :
    refKey St (weakenRef ρ r) = refKey St r := by
  rw [refKey_eq_nodeKey, refKey_eq_nodeKey]
  rfl

/-! ### Composition of first-occurrence keys -/

/-- How the variables of the right part are numbered in a pair, read from the two variable lists:
the variable at position `k` of the right part's list gets its first position in the joined list. -/
def link {V : Type*} [DecidableEq V] (vs ts : List V) (k : ℕ) : ℕ :=
  if h : k < ts.length then (vs ++ ts).idxOf ts[k] else k

/-- **The key of a pair is composed from the keys of its parts** and their variable lists. -/
theorem canon_pair {A V : Type*} [DecidableEq V] (s t : Tm A V) :
    canon (Tm.pair s t) = Tm.pair (canon s) ((canon t).rename (link s.vars t.vars)) := by
  simp only [canon, key, Tm.rename, Tm.vars]
  congr 1
  · apply Tm.rename_congr
    intro v hv
    exact List.idxOf_append_of_mem hv
  · rw [Tm.rename_rename]
    apply Tm.rename_congr
    intro v hv
    have hlt : t.vars.idxOf v < t.vars.length := List.idxOf_lt_length_of_mem hv
    show (s.vars ++ t.vars).idxOf v = link s.vars t.vars (t.vars.idxOf v)
    rw [link, dif_pos hlt, List.getElem_idxOf hlt]

/-! ### Controls -/

namespace ScopedControls

/-- `(f 0 1)`, `(f 5 3)` and `(f 0 0)` with free variables only. -/
def fxy : Term ℕ := .node 7 (.cons 0 (.idx 0) (.cons 0 (.idx 1) .nil))
def fab : Term ℕ := .node 7 (.cons 0 (.idx 5) (.cons 0 (.idx 3) .nil))
def fxx : Term ℕ := .node 7 (.cons 0 (.idx 0) (.cons 0 (.idx 0) .nil))

example : skey fxy = skey fab := by decide
example : skey fxy ≠ skey fxx := by decide

/-- Under one binder: `λ. (g 0 1)`, `λ. (g 0 2)` (variants) and `λ. (g 1 0)` (not a variant: the
bound variable stays bound in its place). -/
def lam (body : Term ℕ) : Term ℕ := .node 1 (.cons 1 body .nil)
def g (a b : Term ℕ) : Term ℕ := .node 2 (.cons 0 a (.cons 0 b .nil))

example : skey (lam (g (.idx 0) (.idx 1))) = skey (lam (g (.idx 0) (.idx 2))) := by decide
example : skey (lam (g (.idx 0) (.idx 1))) ≠ skey (lam (g (.idx 1) (.idx 0))) := by decide

/-- A thinning gives the same key: `rename [false, true] (f 0 1) = (f 1 2)`. -/
example : skey (rename [false, true] fxy) = skey fxy :=
  skey_eq_iff_variant.mpr (fvariant_symm (fvariant_rename _ _))

example : rename [false, true] fxy = .node 7 (.cons 0 (.idx 1) (.cons 0 (.idx 2) .nil)) := by
  decide

end ScopedControls

end Mettapedia.InformationTheory.SymmetryKeys.Scoped
