import Mettapedia.InformationTheory.RelationStoreVariantKeys

/-!
# Terms with argument lists, their variants and their keys

A term is an atom, a variable, or a head applied to a list of arguments.  The MeTTa expression
`(bag (g $x) (h $y))` is `node bag [node g [var x], node h [var y]]`.  An expression whose first
element is not a symbol is a node of a reserved head that lists all its elements.

The terms are written into the binary terms of `RelationStoreVariantKeys` by a prefix encoding
(`enc`): a node is the pair of its head and the spine of its arguments, closed by `nil`.

* `enc_injective`: the encoding loses nothing;
* `enc_rename`: it commutes with renaming;
* `vars_enc`: the variables of the encoding are those of the term, in the same order.

So the keys of `RelationStoreVariantKeys`, read through the encoding, identify exactly the variants
(`ekey_eq_iff_variant`, `ecanon_eq_iff_variant`).  Nothing is proved twice.

* `Variant s t`: each term is an instance of the other by a renaming of its variables.  Example:
  `(f $x $y)` and `(f $a $b)` are variants; `(f $x $x)` and `(f $x $y)` are not.
* `variant_iff_exists_perm`: two terms are variants iff one permutation of the variables carries
  one to the other.  Permutations of the variables act on terms as a group (`MulAction`).
-/

namespace Mettapedia.InformationTheory.SymmetryKeys

open Mettapedia.InformationTheory.RelationStoreVariantKeys

/-- A term: an atom, a variable, or a head applied to a list of arguments. -/
inductive ETm (A V : Type*) where
  | atom : A → ETm A V
  | var : V → ETm A V
  | node : A → List (ETm A V) → ETm A V

/-- The tokens of the encoding: an atom, the head of a node, or the end of an argument list. -/
inductive Tok (A : Type*) where
  | sym : A → Tok A
  | head : A → Tok A
  | nil : Tok A
  deriving DecidableEq

namespace ETm

variable {A V W X : Type*}

/-! ### Renaming and variables -/

mutual

/-- Every variable renamed by `f`. -/
def rename (f : V → W) : ETm A V → ETm A W
  | .atom a => .atom a
  | .var v => .var (f v)
  | .node h args => .node h (renameArgs f args)

/-- `rename` on each argument. -/
def renameArgs (f : V → W) : List (ETm A V) → List (ETm A W)
  | [] => []
  | c :: cs => rename f c :: renameArgs f cs

end

theorem renameArgs_eq_map (f : V → W) (l : List (ETm A V)) :
    renameArgs f l = l.map (rename f) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [renameArgs, ih]

@[simp] theorem rename_atom (f : V → W) (a : A) : (atom a : ETm A V).rename f = atom a := rfl

@[simp] theorem rename_var (f : V → W) (v : V) : (var v : ETm A V).rename f = var (f v) := rfl

@[simp] theorem rename_node (f : V → W) (h : A) (args : List (ETm A V)) :
    (node h args).rename f = node h (args.map (rename f)) := by
  simp [rename, renameArgs_eq_map]

mutual

/-- The variables of a term, one entry per occurrence, left to right. -/
def vars : ETm A V → List V
  | .atom _ => []
  | .var v => [v]
  | .node _ args => varsArgs args

/-- The variables of a list of arguments, one entry per occurrence, left to right. -/
def varsArgs : List (ETm A V) → List V
  | [] => []
  | c :: cs => vars c ++ varsArgs cs

end

theorem varsArgs_eq (l : List (ETm A V)) : varsArgs l = (l.map vars).flatten := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [varsArgs, ih]

@[simp] theorem vars_atom (a : A) : (atom a : ETm A V).vars = [] := rfl

@[simp] theorem vars_var (v : V) : (var v : ETm A V).vars = [v] := rfl

@[simp] theorem vars_node (h : A) (args : List (ETm A V)) :
    (node h args).vars = (args.map vars).flatten := by
  simp [vars, varsArgs_eq]

/-! ### The encoding into binary terms -/

mutual

/-- The prefix encoding: a node is the pair of its head and the spine of its arguments. -/
def enc : ETm A V → Tm (Tok A) V
  | .atom a => .atom (.sym a)
  | .var v => .var v
  | .node h args => .pair (.atom (.head h)) (encArgs args)

/-- The spine of a list of arguments, closed by `nil`. -/
def encArgs : List (ETm A V) → Tm (Tok A) V
  | [] => .atom .nil
  | c :: cs => .pair (enc c) (encArgs cs)

end

mutual

theorem enc_rename (f : V → W) : ∀ t : ETm A V, enc (t.rename f) = (enc t).rename f
  | .atom _ => rfl
  | .var _ => rfl
  | .node h args => by
      simp only [rename, enc, Tm.rename]
      rw [encArgs_rename f args]

theorem encArgs_rename (f : V → W) :
    ∀ l : List (ETm A V), encArgs (renameArgs f l) = (encArgs l).rename f
  | [] => rfl
  | c :: cs => by
      simp only [renameArgs, encArgs, Tm.rename]
      rw [enc_rename f c, encArgs_rename f cs]

end

mutual

theorem vars_enc : ∀ t : ETm A V, (enc t).vars = t.vars
  | .atom _ => rfl
  | .var _ => rfl
  | .node _ args => by
      simp only [enc, Tm.vars, vars, List.nil_append]
      exact varsArgs_enc args

theorem varsArgs_enc : ∀ l : List (ETm A V), (encArgs l).vars = varsArgs l
  | [] => rfl
  | c :: cs => by
      simp only [encArgs, Tm.vars, varsArgs]
      rw [vars_enc c, varsArgs_enc cs]

end

mutual

theorem enc_inj : ∀ s t : ETm A V, enc s = enc t → s = t
  | .atom a, .atom b, e => by
      simp only [enc, Tm.atom.injEq, Tok.sym.injEq] at e
      rw [e]
  | .atom _, .var _, e => by simp [enc] at e
  | .atom _, .node _ _, e => by simp [enc] at e
  | .var _, .atom _, e => by simp [enc] at e
  | .var v, .var w, e => by
      simp only [enc, Tm.var.injEq] at e
      rw [e]
  | .var _, .node _ _, e => by simp [enc] at e
  | .node _ _, .atom _, e => by simp [enc] at e
  | .node _ _, .var _, e => by simp [enc] at e
  | .node h args, .node h' args', e => by
      simp only [enc, Tm.pair.injEq, Tm.atom.injEq, Tok.head.injEq] at e
      rw [e.1, encArgs_inj args args' e.2]

theorem encArgs_inj : ∀ l l' : List (ETm A V), encArgs l = encArgs l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [encArgs] at e
  | _ :: _, [], e => by simp [encArgs] at e
  | c :: cs, d :: ds, e => by
      simp only [encArgs, Tm.pair.injEq] at e
      rw [enc_inj c d e.1, encArgs_inj cs ds e.2]

end

theorem enc_injective : Function.Injective (enc : ETm A V → Tm (Tok A) V) :=
  fun s t e => enc_inj s t e

instance [DecidableEq A] [DecidableEq V] : DecidableEq (ETm A V) := fun s t =>
  decidable_of_iff (enc s = enc t) enc_injective.eq_iff

theorem rename_rename (f : V → W) (g : W → X) (t : ETm A V) :
    (t.rename f).rename g = t.rename (g ∘ f) :=
  enc_injective (by rw [enc_rename, enc_rename, enc_rename, Tm.rename_rename])

@[simp] theorem rename_id (t : ETm A V) : t.rename id = t :=
  enc_injective (by rw [enc_rename, Tm.rename_id])

theorem rename_id' (t : ETm A V) : t.rename (fun v => v) = t := rename_id t

theorem rename_congr {f g : V → W} {t : ETm A V} (h : ∀ v ∈ t.vars, f v = g v) :
    t.rename f = t.rename g :=
  enc_injective (by
    rw [enc_rename, enc_rename]
    exact Tm.rename_congr (by rw [vars_enc]; exact h))

theorem vars_rename (f : V → W) (t : ETm A V) : (t.rename f).vars = t.vars.map f := by
  rw [← vars_enc, enc_rename, Tm.vars_rename, vars_enc]

/-! ### Variants -/

/-- `s` and `t` are variants: each is an instance of the other by renaming its variables. -/
def Variant (s t : ETm A V) : Prop :=
  (∃ f : V → V, s.rename f = t) ∧ ∃ g : V → V, t.rename g = s

theorem variant_iff_enc {s t : ETm A V} : Variant s t ↔ Tm.Variant (enc s) (enc t) := by
  constructor
  · rintro ⟨⟨f, hf⟩, g, hg⟩
    exact ⟨⟨f, by rw [← enc_rename, hf]⟩, g, by rw [← enc_rename, hg]⟩
  · rintro ⟨⟨f, hf⟩, g, hg⟩
    exact ⟨⟨f, enc_injective (by rw [enc_rename, hf])⟩, g,
      enc_injective (by rw [enc_rename, hg])⟩

theorem variant_refl (t : ETm A V) : Variant t t := ⟨⟨id, rename_id t⟩, id, rename_id t⟩

theorem variant_symm {s t : ETm A V} (h : Variant s t) : Variant t s := ⟨h.2, h.1⟩

theorem variant_trans {r s t : ETm A V} (h₁ : Variant r s)
    (h₂ : Variant s t) : Variant r t := by
  obtain ⟨⟨f₁, hf₁⟩, g₁, hg₁⟩ := h₁
  obtain ⟨⟨f₂, hf₂⟩, g₂, hg₂⟩ := h₂
  exact ⟨⟨f₂ ∘ f₁, by rw [← rename_rename, hf₁, hf₂]⟩,
    g₁ ∘ g₂, by rw [← rename_rename, hg₂, hg₁]⟩

/-- A renaming of `s` that has a renaming back is injective on its variables. -/
theorem injOn_of_rename_back {f g : V → V} {s : ETm A V} (hback : (s.rename f).rename g = s) :
    ∀ v ∈ s.vars, ∀ w ∈ s.vars, f v = f w → v = w := by
  have h : ((enc s).rename f).rename g = enc s := by rw [← enc_rename, ← enc_rename, hback]
  have := Tm.injOn_of_rename_back h
  rw [vars_enc] at this
  exact this

/-- **Two terms are variants iff a permutation of the variables carries one to the other.** -/
theorem variant_iff_exists_perm [DecidableEq V] {s t : ETm A V} :
    Variant s t ↔ ∃ σ : Equiv.Perm V, s.rename σ = t := by
  constructor
  · rintro ⟨⟨f, hf⟩, g, hg⟩
    have hinj := injOn_of_rename_back (f := f) (g := g) (s := s) (by rw [hf, hg])
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
      (α := {v // v ∈ s.vars.toFinset}) (fun x => (x : V)) (fun x => f x)
      Subtype.val_injective
      (fun x y hxy => Subtype.ext (hinj _ (List.mem_toFinset.mp x.2) _
        (List.mem_toFinset.mp y.2) hxy))
    refine ⟨σ, ?_⟩
    rw [← hf]
    exact rename_congr fun v hv => hσ ⟨v, List.mem_toFinset.mpr hv⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨⟨σ, rfl⟩, σ.symm, ?_⟩
    rw [rename_rename]
    convert rename_id s
    funext v
    simp

/-- Permutations of the variables act on terms by renaming. -/
instance : MulAction (Equiv.Perm V) (ETm A V) where
  smul σ t := t.rename σ
  one_smul t := by
    show t.rename ⇑(1 : Equiv.Perm V) = t
    rw [Equiv.Perm.coe_one, rename_id]
  mul_smul σ τ t := by
    show t.rename ⇑(σ * τ) = (t.rename τ).rename σ
    rw [rename_rename, Equiv.Perm.coe_mul]

theorem perm_smul_def (σ : Equiv.Perm V) (t : ETm A V) : σ • t = t.rename σ := rfl

/-! ### Keys -/

/-- The key of a term under a numbering: the key of its encoding. -/
def ekey [DecidableEq V] (N : Numbering V) (t : ETm A V) : Tm (Tok A) ℕ := key N (enc t)

/-- **Equal keys exactly on variants**, for a numbering that separates variables and reads only the
pattern in which they recur. -/
theorem ekey_eq_iff_variant [DecidableEq V] {N : Numbering V} (hsep : Separates N)
    (hinv : RenameInvariant N) {s t : ETm A V} : ekey N s = ekey N t ↔ Variant s t :=
  (key_eq_iff_variant hsep hinv).trans variant_iff_enc.symm

/-- The term with each variable numbered by the position of its first occurrence. -/
def ecanon [DecidableEq V] (t : ETm A V) : Tm (Tok A) ℕ := ekey firstOccurrence t

theorem ecanon_eq_iff_variant [DecidableEq V] {s t : ETm A V} :
    ecanon s = ecanon t ↔ Variant s t :=
  ekey_eq_iff_variant idxOf_separates idxOf_renameInvariant

theorem ekey_perm_smul [DecidableEq V] {N : Numbering V} (hsep : Separates N)
    (hinv : RenameInvariant N) (σ : Equiv.Perm V) (t : ETm A V) : ekey N (σ • t) = ekey N t :=
  (ekey_eq_iff_variant hsep hinv).mpr
    (variant_symm (variant_iff_exists_perm.mpr ⟨σ, rfl⟩))

/-! ### Controls -/

/-- `(f $x $y)` and `(f $a $b)` share a key; `(f $x $x)` does not. -/
example : ecanon (A := String) (V := String) (.node "f" [.var "x", .var "y"]) =
    ecanon (.node "f" [.var "a", .var "b"]) := by decide

example : ecanon (A := String) (V := String) (.node "f" [.var "x", .var "x"]) ≠
    ecanon (.node "f" [.var "x", .var "y"]) := by decide

/-- The encoding keeps argument lists apart: `(f (g a))` is not `(f g a)`. -/
example : enc (ETm.node "f" [.node "g" [.atom "a"]] : ETm String String) ≠
    enc (ETm.node "f" [.atom "g", .atom "a"] : ETm String String) := by decide

/-- Argument order is seen by the key: `(bag a b)` and `(bag b a)` differ before any head is
declared unordered. -/
example : ecanon (A := String) (V := String) (.node "bag" [.atom "a", .atom "b"]) ≠
    ecanon (A := String) (V := String) (.node "bag" [.atom "b", .atom "a"]) := by decide

end ETm

end Mettapedia.InformationTheory.SymmetryKeys
