import Mathlib

/-!
# Keys that identify stored terms up to the names of their variables

Two terms are variants when each is an instance of the other by a renaming of
its variables: they differ only in what their variables are called.  A set of
terms that identifies variants needs, for each term, a key that two terms share
exactly when they are variants.  Numbering a term's variables by where they
first occur gives such a key, so a set may store the keys themselves: one
entry per variant, with no second record beside each term.

The result holds for every numbering of a term's variables, read from the list
of their occurrences, that tells distinct variables apart and is unchanged by
renaming the variables injectively:

* `key_eq_iff_variant` : for such a numbering, two terms have equal keys iff
  they are variants;
* `idxOf_separates`, `idxOf_renameInvariant` : the position of a variable's
  first occurrence is such a numbering (`canon_eq_iff_variant`);
* `ordinal_separates`, `ordinal_renameInvariant` : so is the number of distinct
  variables that occur before a variable's first occurrence, the dense
  numbering `0, 1, 2, …` in order of first occurrence (`canonDense_eq_iff_variant`);
* `card_keys_eq_card_classes` : the keys of a finite set of terms are exactly
  as many as the variant classes it meets.

Terms are binary trees over atoms and variables; an expression of several
elements is the spine of its pairs.
-/

namespace Mettapedia.InformationTheory.RelationStoreVariantKeys

/-- A stored term over atoms `A` and variables `V`. -/
inductive Tm (A V : Type*) where
  | atom : A → Tm A V
  | var : V → Tm A V
  | pair : Tm A V → Tm A V → Tm A V
  deriving DecidableEq

namespace Tm

variable {A V W X : Type*}

/-- Every variable renamed by `f`. -/
def rename (f : V → W) : Tm A V → Tm A W
  | atom a => atom a
  | var v => var (f v)
  | pair s t => pair (s.rename f) (t.rename f)

/-- The variables of a term, one entry per occurrence, left to right. -/
def vars : Tm A V → List V
  | atom _ => []
  | var v => [v]
  | pair s t => s.vars ++ t.vars

/-- The shape of a term: its variables erased. -/
def skel (t : Tm A V) : Tm A Unit := t.rename fun _ => ()

@[simp] theorem vars_rename (f : V → W) (t : Tm A V) :
    (t.rename f).vars = t.vars.map f := by
  induction t with
  | atom a => rfl
  | var v => rfl
  | pair s t ihs iht => simp [rename, vars, ihs, iht]

theorem rename_rename (f : V → W) (g : W → X) (t : Tm A V) :
    (t.rename f).rename g = t.rename (g ∘ f) := by
  induction t with
  | atom a => rfl
  | var v => rfl
  | pair s t ihs iht => simp [rename, ihs, iht]

@[simp] theorem rename_id (t : Tm A V) : t.rename id = t := by
  induction t with
  | atom a => rfl
  | var v => rfl
  | pair s t ihs iht => simp [rename, ihs, iht]

theorem rename_congr {f g : V → W} {t : Tm A V} (h : ∀ v ∈ t.vars, f v = g v) :
    t.rename f = t.rename g := by
  induction t with
  | atom a => rfl
  | var v => simpa [rename, vars] using h
  | pair s t ihs iht =>
    simp only [vars, List.mem_append] at h
    simp only [rename]
    rw [ihs fun v hv => h v (Or.inl hv), iht fun v hv => h v (Or.inr hv)]

@[simp] theorem skel_rename (f : V → W) (t : Tm A V) : (t.rename f).skel = t.skel := by
  simp only [skel, rename_rename]

theorem length_vars_eq_of_skel_eq {s : Tm A V} {t : Tm A W} (h : s.skel = t.skel) :
    s.vars.length = t.vars.length := by
  have := congrArg (fun u : Tm A Unit => u.vars.length) h
  simpa [skel] using this

/-- Two renamed terms agree iff the terms have one shape and their variables,
renamed, agree occurrence by occurrence. -/
theorem rename_eq_rename_iff {f : V → X} {g : W → X} {s : Tm A V} {t : Tm A W} :
    s.rename f = t.rename g ↔ s.skel = t.skel ∧ s.vars.map f = t.vars.map g := by
  induction s generalizing t with
  | atom a =>
    cases t <;> simp [rename, skel, vars]
  | var v =>
    cases t <;> simp [rename, skel, vars]
  | pair s₁ s₂ ih₁ ih₂ =>
    cases t with
    | atom a => simp [rename, skel]
    | var w => simp [rename, skel]
    | pair t₁ t₂ =>
      simp only [rename, pair.injEq, ih₁, ih₂, vars, List.map_append]
      constructor
      · rintro ⟨⟨hs₁, hv₁⟩, hs₂, hv₂⟩
        refine ⟨?_, by rw [hv₁, hv₂]⟩
        simp only [skel, rename] at hs₁ hs₂ ⊢
        rw [hs₁, hs₂]
      · rintro ⟨hs, hv⟩
        simp only [skel, rename, pair.injEq] at hs
        have hlen : (s₁.vars.map f).length = (t₁.vars.map g).length := by
          simpa using length_vars_eq_of_skel_eq (s := s₁) (t := t₁) hs.1
        obtain ⟨h₁, h₂⟩ := List.append_inj hv hlen
        exact ⟨⟨hs.1, h₁⟩, hs.2, h₂⟩

/-- `s` and `t` are variants: each is an instance of the other by renaming its
variables. -/
def Variant (s t : Tm A V) : Prop :=
  (∃ f : V → V, s.rename f = t) ∧ ∃ g : V → V, t.rename g = s

theorem variant_refl (t : Tm A V) : Variant t t :=
  ⟨⟨id, rename_id t⟩, ⟨id, rename_id t⟩⟩

theorem variant_symm {s t : Tm A V} (h : Variant s t) : Variant t s :=
  ⟨h.2, h.1⟩

theorem variant_trans {r s t : Tm A V} (h₁ : Variant r s) (h₂ : Variant s t) :
    Variant r t := by
  obtain ⟨⟨f₁, hf₁⟩, g₁, hg₁⟩ := h₁
  obtain ⟨⟨f₂, hf₂⟩, g₂, hg₂⟩ := h₂
  refine ⟨⟨f₂ ∘ f₁, ?_⟩, g₁ ∘ g₂, ?_⟩
  · rw [← rename_rename, hf₁, hf₂]
  · rw [← rename_rename, hg₂, hg₁]

/-- Variance as an equivalence relation. -/
def variantSetoid (A V : Type*) : Setoid (Tm A V) where
  r := Variant
  iseqv := ⟨variant_refl, variant_symm, variant_trans⟩

/-- A renaming of `s` that has a renaming back is injective on its variables. -/
theorem injOn_of_rename_back {f g : V → V} {s : Tm A V}
    (hback : (s.rename f).rename g = s) :
    ∀ v ∈ s.vars, ∀ w ∈ s.vars, f v = f w → v = w := by
  have hid : ∀ v ∈ s.vars, g (f v) = v := by
    rw [rename_rename] at hback
    have h := (rename_eq_rename_iff (f := g ∘ f) (g := id) (s := s) (t := s)).mp
      (by rw [hback, rename_id])
    intro v hv
    have := congrArg (fun l : List V => l) h.2
    have hmap : ∀ u ∈ s.vars, (g ∘ f) u = id u := by
      intro u hu
      exact List.map_eq_map_iff.mp h.2 u hu
    simpa using hmap v hv
  intro v hv w hw hvw
  rw [← hid v hv, ← hid w hw, hvw]

end Tm

open Tm

variable {A V : Type*} [DecidableEq V]

/-- A numbering of variables from the list of their occurrences in a term. -/
abbrev Numbering (V : Type*) := List V → V → ℕ

/-- The numbering tells the variables of a list apart. -/
def Separates (N : Numbering V) : Prop :=
  ∀ (l : List V), ∀ v ∈ l, ∀ w ∈ l, N l v = N l w → v = w

/-- The numbering is unchanged by an injective renaming of the variables: it
reads only the pattern in which they recur. -/
def RenameInvariant (N : Numbering V) : Prop :=
  ∀ (l : List V) (f : V → V), (∀ v ∈ l, ∀ w ∈ l, f v = f w → v = w) →
    ∀ v ∈ l, N (l.map f) (f v) = N l v

/-- The key of a term under a numbering: its variables replaced by their
numbers. -/
def key (N : Numbering V) (t : Tm A V) : Tm A ℕ :=
  t.rename (N t.vars)

/-- The renaming that sends each variable of `s` to the variable at the same
first occurrence in `t`. -/
def alignment (s t : Tm A V) (v : V) : V :=
  if h : s.vars.idxOf v < t.vars.length then t.vars[s.vars.idxOf v] else v

theorem map_alignment {N : Numbering V} (hsep : Separates N) {s t : Tm A V}
    (hlen : s.vars.length = t.vars.length)
    (hmap : s.vars.map (N s.vars) = t.vars.map (N t.vars)) :
    s.vars.map (alignment s t) = t.vars := by
  have hpoint : ∀ k (hs : k < s.vars.length) (ht : k < t.vars.length),
      N s.vars s.vars[k] = N t.vars t.vars[k] := by
    intro k hs ht
    have := congrArg (fun l : List ℕ => l[k]?) hmap
    simpa [List.getElem?_map, hs, ht] using this
  apply List.ext_getElem (by simpa using hlen)
  intro i hi₁ hi₂
  have hi : i < s.vars.length := by simpa using hi₁
  have hmem : s.vars[i] ∈ s.vars := List.getElem_mem hi
  have hj : s.vars.idxOf s.vars[i] < s.vars.length := List.idxOf_lt_length_of_mem hmem
  have hjt : s.vars.idxOf s.vars[i] < t.vars.length := hlen ▸ hj
  have hsj : s.vars[s.vars.idxOf s.vars[i]] = s.vars[i] := List.getElem_idxOf hj
  have hat : (s.vars.map (alignment s t))[i] = t.vars[s.vars.idxOf s.vars[i]] := by
    simp [alignment, hjt]
  rw [hat]
  refine hsep t.vars _ (List.getElem_mem hjt) _ (List.getElem_mem hi₂) ?_
  rw [← hpoint _ hj hjt, ← hpoint _ hi hi₂, hsj]

/-- Two terms have equal keys under a numbering that separates variables and
reads only their pattern iff the terms are variants. -/
theorem key_eq_iff_variant {N : Numbering V} (hsep : Separates N)
    (hinv : RenameInvariant N) {s t : Tm A V} :
    key N s = key N t ↔ Variant s t := by
  constructor
  · intro h
    obtain ⟨hskel, hmap⟩ := rename_eq_rename_iff.mp h
    have hlen := length_vars_eq_of_skel_eq hskel
    refine ⟨⟨alignment s t, ?_⟩, alignment t s, ?_⟩
    · have := (rename_eq_rename_iff (f := alignment s t) (g := id) (s := s) (t := t)).mpr
        ⟨hskel, by rw [map_alignment hsep hlen hmap, List.map_id]⟩
      simpa using this
    · have := (rename_eq_rename_iff (f := alignment t s) (g := id) (s := t) (t := s)).mpr
        ⟨hskel.symm, by rw [map_alignment hsep hlen.symm hmap.symm, List.map_id]⟩
      simpa using this
  · rintro ⟨⟨f, hf⟩, g, hg⟩
    have hinj : ∀ v ∈ s.vars, ∀ w ∈ s.vars, f v = f w → v = w :=
      injOn_of_rename_back (g := g) (by rw [hf, hg])
    subst hf
    unfold key
    rw [vars_rename, rename_rename]
    exact (rename_congr fun v hv => (hinv s.vars f hinj v hv)).symm

/-! ### First occurrences -/

/-- Number each variable by the position of its first occurrence. -/
def firstOccurrence : Numbering V := fun l v => l.idxOf v

theorem idxOf_separates : Separates (firstOccurrence (V := V)) := by
  intro l v hv w hw h
  have hv' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)
  have hw' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hw)
  simp only [firstOccurrence] at h
  rw [← hv', ← hw']
  simp only [h]

theorem idxOf_map_of_injOn (l : List V) (f : V → V)
    (hinj : ∀ v ∈ l, ∀ w ∈ l, f v = f w → v = w) :
    ∀ v ∈ l, (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro v hv
    have hxs : ∀ v ∈ xs, ∀ w ∈ xs, f v = f w → v = w := fun v hv w hw =>
      hinj v (List.mem_cons_of_mem _ hv) w (List.mem_cons_of_mem _ hw)
    by_cases hxv : x = v
    · subst hxv
      simp
    · have hfx : f x ≠ f v := fun h =>
        hxv (hinj x List.mem_cons_self v hv h)
      have hv' : v ∈ xs := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h.symm hxv
        · exact h
      rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih hxs v hv']
      simp only [beq_eq_false_iff_ne.mpr hfx, beq_eq_false_iff_ne.mpr hxv,
        cond_false]

theorem idxOf_renameInvariant : RenameInvariant (firstOccurrence (V := V)) :=
  fun l f hinj v hv => idxOf_map_of_injOn l f hinj v hv

/-- A term with each variable numbered by the position of its first
occurrence. -/
def canon (t : Tm A V) : Tm A ℕ := key firstOccurrence t

theorem canon_eq_iff_variant {s t : Tm A V} : canon s = canon t ↔ Variant s t :=
  key_eq_iff_variant idxOf_separates idxOf_renameInvariant

/-! ### Dense numbering in order of first occurrence -/

/-- Number each variable by how many distinct variables occur before its first
occurrence: `0, 1, 2, …` in order of first occurrence. -/
def ordinal : Numbering V := fun l v => (l.take (l.idxOf v)).toFinset.card

theorem ordinal_separates : Separates (ordinal (V := V)) := by
  intro l v hv w hw h
  by_contra hne
  have hiv := List.idxOf_lt_length_of_mem hv
  have hiw := List.idxOf_lt_length_of_mem hw
  have hdiff : l.idxOf v ≠ l.idxOf w := fun hvw => hne <| by
    rw [← List.getElem_idxOf hiv, ← List.getElem_idxOf hiw]
    simp only [hvw]
  -- The earlier first occurrence lies in the later one's prefix and not in
  -- its own, so the later one counts strictly more distinct variables.
  have key_lt : ∀ a b, a ∈ l → b ∈ l → l.idxOf a < l.idxOf b →
      (l.take (l.idxOf a)).toFinset.card < (l.take (l.idxOf b)).toFinset.card := by
    intro a b ha hb hab
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨a, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_toFinset] at hx ⊢
      exact List.take_subset_take_left l (Nat.le_of_lt hab) hx
    · simp only [List.mem_toFinset]
      have hia := List.idxOf_lt_length_of_mem ha
      rw [List.mem_take_iff_getElem]
      exact ⟨l.idxOf a, by simp [hab, hia], List.getElem_idxOf hia⟩
    · simp only [List.mem_toFinset]
      intro hin
      rw [List.mem_take_iff_getElem] at hin
      obtain ⟨i, hi, hia⟩ := hin
      have hlt : i < l.idxOf a := by
        simp only [lt_min_iff] at hi
        exact hi.1
      have hne := List.not_of_lt_findIdx (p := (· == a)) (xs := l) hlt
      simp only [beq_eq_false_iff_ne] at hne
      exact hne hia
  rcases Nat.lt_or_gt_of_ne hdiff with hlt | hlt
  · exact absurd h (Nat.ne_of_lt (key_lt v w hv hw hlt))
  · exact absurd h (Nat.ne_of_gt (key_lt w v hw hv hlt))

theorem ordinal_renameInvariant : RenameInvariant (ordinal (V := V)) := by
  intro l f hinj v hv
  simp only [ordinal]
  rw [idxOf_map_of_injOn l f hinj v hv, ← List.map_take]
  have himage : ((l.take (l.idxOf v)).map f).toFinset =
      (l.take (l.idxOf v)).toFinset.image f := by
    rw [List.toFinset, List.toFinset, ← Multiset.map_coe, Multiset.toFinset_map]
  rw [himage]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  simp only [Finset.mem_coe, List.mem_toFinset] at hx hy
  exact hinj x (List.mem_of_mem_take hx) y (List.mem_of_mem_take hy) hxy

/-- A term with its variables numbered `0, 1, 2, …` in order of first
occurrence. -/
def canonDense (t : Tm A V) : Tm A ℕ := key ordinal t

theorem canonDense_eq_iff_variant {s t : Tm A V} :
    canonDense s = canonDense t ↔ Variant s t :=
  key_eq_iff_variant ordinal_separates ordinal_renameInvariant

/-! ### One key per variant class -/

/-- The variant classes of terms map into keys injectively. -/
theorem key_quotient_injective {N : Numbering V} (hsep : Separates N)
    (hinv : RenameInvariant N) :
    Function.Injective
      (Quotient.lift (s := variantSetoid A V) (key N)
        fun _ _ h => (key_eq_iff_variant hsep hinv).mpr h) := by
  intro x y hxy
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  exact Quotient.sound ((key_eq_iff_variant hsep hinv).mp hxy)

open Classical in
/-- A finite set of terms has exactly as many keys as the variant classes it
meets: a set that stores keys holds one entry per variant. -/
theorem card_keys_eq_card_classes [DecidableEq A] {N : Numbering V}
    (hsep : Separates N) (hinv : RenameInvariant N) (S : Finset (Tm A V)) :
    (S.image (key N)).card =
      (S.image (Quotient.mk (variantSetoid A V))).card := by
  classical
  have hfactor : S.image (key N) =
      (S.image (Quotient.mk (variantSetoid A V))).image
        (Quotient.lift (s := variantSetoid A V) (key N)
          fun _ _ h => (key_eq_iff_variant hsep hinv).mpr h) := by
    rw [Finset.image_image]
    rfl
  rw [hfactor, Finset.card_image_of_injective _ (key_quotient_injective hsep hinv)]

/-! ### Examples -/

/-- `(f $x $y)` and `(f $a $b)` share a key; `(f $x $x)` does not. -/
example : canonDense (A := String) (V := String)
      (.pair (.atom "f") (.pair (.var "x") (.var "y"))) =
    canonDense (.pair (.atom "f") (.pair (.var "a") (.var "b"))) := by
  decide

example : canonDense (A := String) (V := String)
      (.pair (.atom "f") (.pair (.var "x") (.var "x"))) ≠
    canonDense (.pair (.atom "f") (.pair (.var "x") (.var "y"))) := by
  decide

end Mettapedia.InformationTheory.RelationStoreVariantKeys
