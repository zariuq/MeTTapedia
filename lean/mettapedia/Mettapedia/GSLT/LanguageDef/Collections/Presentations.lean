import Mettapedia.Algebra.Collections.Ornaments
import Mettapedia.GSLT.LanguageDef.Collections.CoreList
import Mettapedia.GSLT.LanguageDef.Collections.Layouts

/-!
# Constructor families present lists

A user datatype whose constructors each have at most one recursive argument is
a list of the data at its cells, followed by the term that ends the chain
(`Algebra.Collections.Ornaments.Linear.spineEquiv`). This module states that
fact on the terms of a dialect, where nothing marks a datatype, and derives
from it the laws a runtime needs to store such a datatype as a native
sequence, once for every datatype.

A **constructor family** on terms `T` builds a cell from its fields and its
recursive argument and recognizes the terms that are cells (`Family`):
`uncell` inverts `cell` and accepts nothing else, and the recursive argument
of a cell is smaller. HE's `(Cons $head $tail)`, a grammar's
`(bnf-v1:entries-cons $head $tail)` and Peano's `(S $n)` are families
(`last`, `binary`, `unary`). Two families with disjoint cells form one
(`Family.sum`), and families of distinct heads or arities are disjoint
(`last_disjoint`), so a single assignment of recursive positions to heads
covers every datatype of a program, including chains that mix constructors.

* **Spines.** Every term is uniquely a maximal chain of cells followed by a
  term that is not a cell (`Family.equivCanonical`): `Family.spine` reads the
  chain, `Family.build` writes it back (`Family.build_spine`,
  `Family.spine_build_of_canonical`). A spine whose end is itself a cell
  denotes the same term as the longer spine
  (`Family.spine_build`): replacing the end of a spine by a spine appends.
* **Operations as folds.** An observation that takes one step per cell is a
  right fold over the spine (`Family.fold_build`), and structural recursion
  written as one equation per case is that fold (`Family.recurse_eq_foldr`).
  Length, indexing, printing, fingerprints, cached type judgments and
  normal-form flags are such observations. A recursion whose step rebuilds a
  cell rebuilds the spine with a new end (`Family.recurse_cell`): appending,
  for lists, and addition, for numerals (`plus_numeral`).
* **Substitution.** A substitution that commutes with cells changes the
  fields elementwise and can only extend the spine at its end
  (`Family.spine_map_build`). On HE terms the end extends when it is a
  variable bound to a cell, and also when it is an expression whose head is a
  variable (`Controls.variable_head_becomes_cell`).
* **One contract for every family.** A family whose cells hold one term, with
  an end that is not a cell, manifests the core list
  (`Family.manifestation`, `Family.contract`), so it agrees with every other
  manifestation, HE's expressions among them, on length, indexing and head
  (`CoreList.Contract.agree`). Its canonical spines form a layout in the sense
  of `Layouts.Layout` (`Family.layout`); on HE terms the layout's abstraction,
  elements with `nil`, a variable or an improper end, determines the term
  (`he_layout_abs_injective`).
* **Numerals are counts.** A family whose cells have no fields has spines that
  are numbers of cells (`spine_numeral`); numerals are injective in their
  count (`numeral_injective`).
* **Indices that survive suffix views.** The polynomial fingerprint of every
  suffix is recovered from the fingerprint of the whole
  (`fingerprintOf_drop`), since each of its steps is a bijection.

Controls: a user's own `Cons`/`Nil` list and the grammar's entries list
satisfy the contract by instantiation (`Controls.cons_nil_contract`,
`Controls.entries_contract`) and agree with HE's expression of the same
elements (`Controls.user_list_agrees_with_expression`). Erasing the family
identifies distinct terms (`Controls.family_erasure_identifies`); spines that
are not maximal denote one term twice (`Controls.noncanonical_spines`); an
end that is a cell breaks the contract (`Controls.cell_end_breaks_contract`);
a bounded count identifies distinct numerals
(`Controls.bounded_numerals_collide`); a chain mixing two constructors is one
spine of their sum (`Controls.mixed_chain`); a binary tree's spine follows one
child, so its length is not the number of nodes
(`Controls.tree_spine_is_not_size`); trees read as finite maps, and lists read
as bags, identify terms a pattern distinguishes (`Controls.trees_as_maps`,
`Controls.lists_as_bags`), while a fold into bags is invariant under
reordering (`Controls.bag_fold_reorders`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.Presentations

universe u v w

/-- A constructor family on terms `T` with fields `F`. -/
structure Family (T : Type u) (F : Type v) where
  /-- The cell with these fields and this recursive argument. -/
  cell : F → T → T
  /-- The fields and recursive argument of a cell, and nothing for other terms. -/
  uncell : T → Option (F × T)
  uncell_cell : ∀ f r, uncell (cell f r) = some (f, r)
  cell_uncell : ∀ {t f r}, uncell t = some (f, r) → cell f r = t
  /-- A measure that decreases from a cell to its recursive argument. -/
  rank : T → ℕ
  rank_lt : ∀ {t f r}, uncell t = some (f, r) → rank r < rank t

/-- The fields of a chain of cells, outermost first, and the term that ends it. -/
@[ext]
structure Spine (T : Type u) (F : Type v) where
  elems : List F
  stop : T

namespace Family

variable {T : Type u} {F : Type v} (P : Family T F)

/-- The term a spine denotes. -/
def build (s : Spine T F) : T := s.elems.foldr P.cell s.stop

@[simp] theorem build_nil (e : T) : P.build ⟨[], e⟩ = e := rfl

@[simp] theorem build_cons (f : F) (fs : List F) (e : T) :
    P.build ⟨f :: fs, e⟩ = P.cell f (P.build ⟨fs, e⟩) := rfl

/-- The maximal spine of a term: follow cells to the first term that is not
a cell. -/
def spine (t : T) : Spine T F :=
  match _h : P.uncell t with
  | some (f, r) => ⟨f :: (spine r).elems, (spine r).stop⟩
  | none => ⟨[], t⟩
termination_by P.rank t
decreasing_by exact P.rank_lt _h

theorem spine_of_some {t : T} {f : F} {r : T} (h : P.uncell t = some (f, r)) :
    P.spine t = ⟨f :: (P.spine r).elems, (P.spine r).stop⟩ := by
  rw [spine]
  split
  · next f' r' h' => rw [h] at h'; cases h'; rfl
  · next h' => rw [h] at h'; cases h'

theorem spine_of_none {t : T} (h : P.uncell t = none) : P.spine t = ⟨[], t⟩ := by
  rw [spine]
  split
  · next f' r' h' => rw [h] at h'; cases h'
  · rfl

@[simp] theorem spine_cell (f : F) (r : T) :
    P.spine (P.cell f r) = ⟨f :: (P.spine r).elems, (P.spine r).stop⟩ :=
  P.spine_of_some (P.uncell_cell f r)

/-- A spine is canonical when its end is not a cell. -/
def Canonical (s : Spine T F) : Prop := P.uncell s.stop = none

theorem build_spine (t : T) : P.build (P.spine t) = t := by
  match h : P.uncell t with
  | some (f, r) =>
      rw [P.spine_of_some h]
      change P.cell f (P.build (P.spine r)) = t
      rw [build_spine r]
      exact P.cell_uncell h
  | none => rw [P.spine_of_none h]; rfl
termination_by P.rank t
decreasing_by exact P.rank_lt h

theorem spine_canonical (t : T) : P.Canonical (P.spine t) := by
  match h : P.uncell t with
  | some (f, r) =>
      rw [P.spine_of_some h]
      exact spine_canonical r
  | none => rw [P.spine_of_none h]; exact h
termination_by P.rank t
decreasing_by exact P.rank_lt h

/-- **Splicing.** The maximal spine of a spine's term is its fields followed by
the maximal spine of its end. -/
theorem spine_build (s : Spine T F) :
    P.spine (P.build s) = ⟨s.elems ++ (P.spine s.stop).elems, (P.spine s.stop).stop⟩ := by
  obtain ⟨fs, e⟩ := s
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [build_cons, spine_cell, ih]; rfl

theorem spine_build_of_canonical {s : Spine T F} (canonical : P.Canonical s) :
    P.spine (P.build s) = s := by
  rw [spine_build, P.spine_of_none canonical]
  simp

/-- **Every term is one canonical spine.** -/
def equivCanonical : T ≃ {s : Spine T F // P.Canonical s} where
  toFun t := ⟨P.spine t, P.spine_canonical t⟩
  invFun s := P.build s.1
  left_inv := P.build_spine
  right_inv s := Subtype.ext (P.spine_build_of_canonical s.2)

/-- Replacing the end of a spine by a spine appends. -/
theorem build_append (fs gs : List F) (e : T) :
    P.build ⟨fs, P.build ⟨gs, e⟩⟩ = P.build ⟨fs ++ gs, e⟩ := by
  simp [build, List.foldr_append]

/-- The suffix after one cell is the recursive argument. -/
theorem uncell_build (f : F) (fs : List F) (e : T) :
    P.uncell (P.build ⟨f :: fs, e⟩) = some (f, P.build ⟨fs, e⟩) :=
  P.uncell_cell f _

/-! ### Operations as folds -/

/-- **The fold law.** An observation that takes one step per cell is a right
fold over the spine. -/
theorem fold_build {β : Type w} (g : T → β) (step : F → β → β)
    (cell_step : ∀ f r, g (P.cell f r) = step f (g r)) (s : Spine T F) :
    g (P.build s) = s.elems.foldr step (g s.stop) := by
  obtain ⟨fs, e⟩ := s
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [build_cons, cell_step, ih]; rfl

theorem fold_spine {β : Type w} (g : T → β) (step : F → β → β)
    (cell_step : ∀ f r, g (P.cell f r) = step f (g r)) (t : T) :
    g t = (P.spine t).elems.foldr step (g (P.spine t).stop) := by
  conv_lhs => rw [← P.build_spine t]
  exact P.fold_build g step cell_step _

/-- Structural recursion over a family, as two equations read in order:
`(g (c $f $r)) = (step $f (g $r))` and `(g $other) = (final $other)`. -/
def recurse {β : Type w} (step : F → β → β) (final : T → β) (t : T) : β :=
  match _h : P.uncell t with
  | some (f, r) => step f (recurse step final r)
  | none => final t
termination_by P.rank t
decreasing_by exact P.rank_lt _h

theorem recurse_cell_eq {β : Type w} (step : F → β → β) (final : T → β) (f : F) (r : T) :
    P.recurse step final (P.cell f r) = step f (P.recurse step final r) := by
  rw [recurse]
  split
  · next f' r' h' => rw [P.uncell_cell] at h'; cases h'; rfl
  · next h' => rw [P.uncell_cell] at h'; cases h'

theorem recurse_of_none {β : Type w} (step : F → β → β) (final : T → β) {t : T}
    (h : P.uncell t = none) : P.recurse step final t = final t := by
  rw [recurse]
  split
  · next f' r' h' => rw [h] at h'; cases h'
  · rfl

/-- **Authored structural recursion is the native right fold over the spine.** -/
theorem recurse_eq_foldr {β : Type w} (step : F → β → β) (final : T → β) (t : T) :
    P.recurse step final t = (P.spine t).elems.foldr step (final (P.spine t).stop) := by
  rw [P.fold_spine (P.recurse step final) step (P.recurse_cell_eq step final) t,
    P.recurse_of_none step final (P.spine_canonical t)]

/-- A recursion whose step rebuilds a cell rebuilds the spine with a new end. -/
theorem recurse_cell (final : T → T) (t : T) :
    P.recurse (fun f r => P.cell f r) final t = P.build ⟨(P.spine t).elems, final (P.spine t).stop⟩ :=
  P.recurse_eq_foldr _ final t

/-! ### Substitution -/

/-- **Substitution extends spines only at their end.** For a map of terms that
commutes with cells, the maximal spine of the image is the mapped fields
followed by the maximal spine of the image of the end. -/
theorem spine_map_build (σ : T → T) (m : F → F)
    (natural : ∀ f r, σ (P.cell f r) = P.cell (m f) (σ r)) (s : Spine T F) :
    P.spine (σ (P.build s)) =
      ⟨s.elems.map m ++ (P.spine (σ s.stop)).elems, (P.spine (σ s.stop)).stop⟩ := by
  have image : σ (P.build s) = P.build ⟨s.elems.map m, σ s.stop⟩ := by
    rw [P.fold_build σ (fun f x => P.cell (m f) x) natural s]
    simp [build, List.foldr_map]
  rw [image, spine_build]

/-! ### Families on the same terms -/

/-- A family with its fields renamed along an equivalence. -/
def reindex {G : Type w} (e : F ≃ G) : Family T G where
  cell g r := P.cell (e.symm g) r
  uncell t := (P.uncell t).map fun p => (e p.1, p.2)
  uncell_cell g r := by simp [P.uncell_cell]
  cell_uncell {t g r} h := by
    obtain ⟨⟨f, r'⟩, hu, hp⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simpa using P.cell_uncell hu
  rank := P.rank
  rank_lt {t g r} h := by
    obtain ⟨⟨f, r'⟩, hu, hp⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    exact P.rank_lt hu

/-- Two families with disjoint cells and one rank form a family whose cells
are the cells of either. -/
def sum {G : Type w} (Q : Family T G)
    (disjoint : ∀ {t f r}, P.uncell t = some (f, r) → Q.uncell t = none)
    (same_rank : P.rank = Q.rank) : Family T (F ⊕ G) where
  cell
    | .inl f, r => P.cell f r
    | .inr g, r => Q.cell g r
  uncell t :=
    match P.uncell t with
    | some (f, r) => some (.inl f, r)
    | none => (Q.uncell t).map fun p => (.inr p.1, p.2)
  uncell_cell
    | .inl f, r => by simp [P.uncell_cell]
    | .inr g, r => by
        cases hP : P.uncell (Q.cell g r) with
        | none => simp [Q.uncell_cell]
        | some p =>
            have := disjoint hP
            rw [Q.uncell_cell] at this
            cases this
  cell_uncell {t fg r} h := by
    cases hP : P.uncell t with
    | some p =>
        obtain ⟨f, r'⟩ := p
        rw [hP] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact P.cell_uncell hP
    | none =>
        rw [hP] at h
        obtain ⟨⟨g, r'⟩, hu, hp⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact Q.cell_uncell hu
  rank := P.rank
  rank_lt {t fg r} h := by
    cases hP : P.uncell t with
    | some p =>
        obtain ⟨f, r'⟩ := p
        rw [hP] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact P.rank_lt hP
    | none =>
        rw [hP] at h
        obtain ⟨⟨g, r'⟩, hu, hp⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        rw [same_rank]
        exact Q.rank_lt hu

/-! ### Families whose cells hold one term -/

section OneField

variable (P : Family T T) [DecidableEq T]

/-- The elements of a term read as a list ending in `nil`. -/
def read (nil : T) (t : T) : Option (List T) :=
  if (P.spine t).stop = nil then some (P.spine t).elems else none

/-- The core list manifested by the family, with `nil` as its end. -/
def manifestation (nil : T) : CoreList.Manifestation T where
  write xs := P.build ⟨xs, nil⟩
  read := P.read nil
  length t := (P.read nil t).map List.length
  nth t i := (P.read nil t).bind (·[i]?)
  head t := (P.read nil t).bind List.head?
  tail t := (P.read nil t).bind fun
    | [] => none
    | _ :: rest => some (P.build ⟨rest, nil⟩)

theorem read_build (nil : T) (nil_end : P.uncell nil = none) (xs : List T) :
    P.read nil (P.build ⟨xs, nil⟩) = some xs := by
  simp [read, P.spine_build_of_canonical (s := ⟨xs, nil⟩) nil_end]

/-- **One contract for every family.** -/
theorem contract (nil : T) (nil_end : P.uncell nil = none) :
    CoreList.Contract (P.manifestation nil) where
  read_write xs := P.read_build nil nil_end xs
  write_read t xs accepted := by
    change P.read nil t = some xs at accepted
    unfold read at accepted
    split at accepted
    · next stop =>
        simp only [Option.some.injEq] at accepted
        change P.build ⟨xs, nil⟩ = t
        rw [← accepted, ← stop]
        exact P.build_spine t
    · cases accepted
  length_write xs := by simp [manifestation, P.read_build nil nil_end]
  nth_write xs i := by simp [manifestation, P.read_build nil nil_end]
  head_write xs := by simp [manifestation, P.read_build nil nil_end]
  tail_write x xs := by
    change (P.read nil (P.build ⟨x :: xs, nil⟩)).bind _ = _
    rw [P.read_build nil nil_end]
    rfl

end OneField

section Layout

variable (P : Family T T)

/-- The canonical spines of the family as a layout of list values, reading
the end through `classify`. -/
def layout {V : Type w} (classify : T → Layouts.Terminal T V) : Layouts.Layout T V where
  Carrier := {s : Spine T T // P.Canonical s}
  abs s := (s.1.elems, classify s.1.stop)
  cons a s := ⟨⟨a :: s.1.elems, s.1.stop⟩, s.2⟩
  head s := s.1.elems.head?
  tail s := s.1.elems.tail?.map fun rest => ⟨⟨rest, s.1.stop⟩, s.2⟩
  nth s i := s.1.elems[i]?
  knownLength s := s.1.elems.length
  abs_cons _ _ := rfl
  head_spec _ := rfl
  tail_spec s := by simp [Option.map_map, Function.comp_def]
  nth_spec _ _ := rfl
  knownLength_spec _ := rfl

/-- With an injective reading of ends, the layout's abstraction determines the
term. -/
theorem layout_abs_injective {V : Type w} (classify : T → Layouts.Terminal T V)
    (injective : Function.Injective classify) :
    Function.Injective (P.layout classify).abs := by
  intro s₁ s₂ same
  simp only [layout, Prod.mk.injEq] at same
  exact Subtype.ext (Spine.ext same.1 (injective same.2))

end Layout

end Family

/-! ## Fingerprints of suffix views -/

section Fingerprint

variable {A : Type u} {V : Type v} {R : Type w} [CommRing R]

/-- One fingerprint step, `acc ↦ c + B · acc`: a bijection when `B` is a unit. -/
def affineStep (B : Rˣ) (c : R) : Equiv.Perm R where
  toFun acc := c + B * acc
  invFun acc := ↑B⁻¹ * (acc - c)
  left_inv acc := by simp [← mul_assoc]
  right_inv acc := by simp [← mul_assoc]

theorem fingerprintOf_eq_foldr (B : Rˣ) (element : A → R) (terminal : Layouts.Terminal A V → R)
    (end_ : Layouts.Terminal A V) (xs : List A) :
    Layouts.fingerprintOf (B : R) element terminal end_ xs =
      xs.foldr (fun x acc => affineStep B (element x) acc) (terminal end_) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [Layouts.fingerprintOf, ih, List.foldr_cons]; rfl

/-- **The fingerprint of every suffix** is the fingerprint of the whole with
the dropped steps undone. -/
theorem fingerprintOf_drop (B : Rˣ) (element : A → R) (terminal : Layouts.Terminal A V → R)
    (end_ : Layouts.Terminal A V) (xs : List A) (i : ℕ) :
    Layouts.fingerprintOf (B : R) element terminal end_ (xs.drop i) =
      ((xs.take i).map fun x => affineStep B (element x)).prod⁻¹
        (Layouts.fingerprintOf (B : R) element terminal end_ xs) := by
  rw [fingerprintOf_eq_foldr, fingerprintOf_eq_foldr]
  exact Algebra.Collections.Ornaments.foldr_drop_of_perm
    (fun x => affineStep B (element x)) (terminal end_) xs i

end Fingerprint

/-! ## HE families -/

section HE

open Mettapedia.Languages.MeTTa.OSLFCore

/-- The fields of a cell that has `m` of them. -/
abbrev Fields (m : ℕ) := {fs : List Atom // fs.length = m}

mutual
/-- The number of nodes of an atom. -/
def nodes : Atom → ℕ
  | .expression xs => nodesAll xs + 1
  | _ => 1

/-- The number of nodes of a list of atoms. -/
def nodesAll : List Atom → ℕ
  | [] => 0
  | x :: xs => nodes x + nodesAll xs
end

theorem nodesAll_append (xs ys : List Atom) : nodesAll (xs ++ ys) = nodesAll xs + nodesAll ys := by
  induction xs with
  | nil => simp [nodesAll]
  | cons x xs ih => simp [nodesAll, ih]; omega

/-- Recognize the elements `c x₁ … xₘ r` of an expression. -/
def lastArgs (c : String) (m : ℕ) : List Atom → Option (Fields m × Atom)
  | [] => none
  | head :: args =>
      if head = .symbol c then
        match args.reverse with
        | [] => none
        | r :: before =>
            if h : before.length = m then some (⟨before.reverse, by simp [h]⟩, r) else none
      else none

/-- Recognize `(c x₁ … xₘ r)`. -/
def lastUncell (c : String) (m : ℕ) : Atom → Option (Fields m × Atom)
  | .expression xs => lastArgs c m xs
  | _ => none

theorem lastArgs_eq_some {c : String} {m : ℕ} {xs : List Atom} {fs : Fields m} {r : Atom} :
    lastArgs c m xs = some (fs, r) ↔ xs = .symbol c :: (fs.1 ++ [r]) := by
  obtain ⟨fs, hfs⟩ := fs
  constructor
  · intro h
    match xs with
    | [] => cases h
    | head :: args =>
        simp only [lastArgs] at h
        split_ifs at h with hc
        subst hc
        split at h
        · cases h
        · next r' before reversed =>
            split_ifs at h with hb
            simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have : args = (r' :: before).reverse := by rw [← reversed, List.reverse_reverse]
            simp [this]
  · rintro rfl
    simp [lastArgs, hfs]

theorem lastUncell_eq_some {c : String} {m : ℕ} {t : Atom} {fs : Fields m} {r : Atom} :
    lastUncell c m t = some (fs, r) ↔ t = .expression (.symbol c :: (fs.1 ++ [r])) := by
  cases t with
  | expression xs => simp only [lastUncell, lastArgs_eq_some, Atom.expression.injEq]
  | symbol _ => simp [lastUncell]
  | var _ => simp [lastUncell]
  | grounded _ => simp [lastUncell]

/-- The family of the constructor `c` with `m` fields before its recursive
argument, which comes last: cells `(c x₁ … xₘ r)`. -/
def last (c : String) (m : ℕ) : Family Atom (Fields m) where
  cell fs r := .expression (.symbol c :: (fs.1 ++ [r]))
  uncell := lastUncell c m
  uncell_cell fs r := lastUncell_eq_some.mpr rfl
  cell_uncell h := (lastUncell_eq_some.mp h).symm
  rank := nodes
  rank_lt {t fs r} h := by
    rw [lastUncell_eq_some.mp h]
    simp only [nodes, nodesAll, nodesAll_append]
    omega

theorem last_uncell (c : String) (m : ℕ) : (last c m).uncell = lastUncell c m := rfl

/-- **Distinct heads or arities give disjoint families**, all with the rank
`nodes`, so any finite assignment of recursive positions to pairs of a head and
an arity is one family, an iterated `Family.sum`. -/
theorem last_disjoint {c₁ c₂ : String} {m₁ m₂ : ℕ} (distinct : c₁ ≠ c₂ ∨ m₁ ≠ m₂) {t : Atom}
    {fs : Fields m₁} {r : Atom} (h : (last c₁ m₁).uncell t = some (fs, r)) :
    (last c₂ m₂).uncell t = none := by
  have shape := lastUncell_eq_some.mp h
  subst shape
  cases hu : (last c₂ m₂).uncell (.expression (.symbol c₁ :: (fs.1 ++ [r]))) with
  | none => rfl
  | some p =>
      obtain ⟨gs, r'⟩ := p
      rw [last_uncell] at hu
      have same := lastUncell_eq_some.mp hu
      simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨heads, rest⟩ := same
      rcases distinct with different | different
      · exact absurd heads different
      · have lengths := congrArg List.length rest
        simp [fs.2, gs.2] at lengths
        exact absurd lengths different

/-- One field is one term. -/
def fieldsOne : Fields 1 ≃ Atom where
  toFun fs := fs.1[0]'(by rw [fs.2]; exact Nat.one_pos)
  invFun a := ⟨[a], rfl⟩
  left_inv fs := by
    obtain ⟨fs, hfs⟩ := fs
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hfs
    rfl
  right_inv _ := rfl

/-- No fields. -/
def fieldsZero : Fields 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], rfl⟩
  left_inv fs := by
    obtain ⟨fs, hfs⟩ := fs
    exact Subtype.ext (List.eq_nil_of_length_eq_zero hfs).symm
  right_inv _ := rfl

/-- Cells `(c x r)`: `(Cons $head $tail)`. -/
def binary (c : String) : Family Atom Atom := (last c 1).reindex fieldsOne

/-- Cells `(c r)`: `(S $n)`. -/
def unary (c : String) : Family Atom Unit := (last c 0).reindex fieldsZero

@[simp] theorem binary_cell (c : String) (x r : Atom) :
    (binary c).cell x r = .expression [.symbol c, x, r] := rfl

@[simp] theorem unary_cell (c : String) (u : Unit) (r : Atom) :
    (unary c).cell u r = .expression [.symbol c, r] := rfl

mutual
/-- Replace the variables that `σ` binds. -/
def substitute (σ : String → Option Atom) : Atom → Atom
  | .var v => (σ v).getD (.var v)
  | .expression xs => .expression (substituteAll σ xs)
  | .symbol s => .symbol s
  | .grounded g => .grounded g

/-- Replace the variables that `σ` binds, in each atom of a list. -/
def substituteAll (σ : String → Option Atom) : List Atom → List Atom
  | [] => []
  | x :: xs => substitute σ x :: substituteAll σ xs
end

theorem substitute_expression (σ : String → Option Atom) (xs : List Atom) :
    substitute σ (.expression xs) = .expression (xs.map (substitute σ)) := by
  rw [substitute]
  congr 1
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [substituteAll, ih]; rfl

/-- Substitution commutes with the cells of every `last` family. -/
theorem substitute_cell (σ : String → Option Atom) (c : String) (m : ℕ) (fs : Fields m) (r : Atom) :
    substitute σ ((last c m).cell fs r) =
      (last c m).cell ⟨fs.1.map (substitute σ), by simp [fs.2]⟩ (substitute σ r) := by
  simp only [last, substitute_expression, List.map_cons, List.map_append, List.map_nil]
  rfl

/-- On HE terms, substitution extends a spine only at its end. -/
theorem spine_substitute (σ : String → Option Atom) (c : String) (m : ℕ) (s : Spine Atom (Fields m)) :
    (last c m).spine (substitute σ ((last c m).build s)) =
      ⟨s.elems.map (fun fs => ⟨fs.1.map (substitute σ), by simp [fs.2]⟩) ++
          ((last c m).spine (substitute σ s.stop)).elems,
        ((last c m).spine (substitute σ s.stop)).stop⟩ :=
  (last c m).spine_map_build (substitute σ) _ (substitute_cell σ c m) s

/-- How the end of a list value reads: its `nil`, a variable, or an improper end. -/
def terminalOf (nil : Atom) (t : Atom) : Layouts.Terminal Atom String :=
  if t = nil then .nil else
    match t with
    | .var v => .var v
    | other => .improper other

theorem terminalOf_injective (nil : Atom) : Function.Injective (terminalOf nil) := by
  intro t₁ t₂ same
  unfold terminalOf at same
  split_ifs at same with h₁ h₂ h₂
  · rw [h₁, h₂]
  · cases t₂ <;> simp at same
  · cases t₁ <;> simp at same
  · cases t₁ <;> cases t₂ <;> simp_all

/-- **On HE terms the spine layout's abstraction determines the term**, so an
observation of the abstraction, as `Layouts.Layout.agree` compares them, is an
observation of the term. -/
theorem he_layout_abs_injective (c : String) (nil : Atom) :
    Function.Injective ((binary c).layout (terminalOf nil)).abs :=
  (binary c).layout_abs_injective _ (terminalOf_injective nil)

/-! ### Numerals -/

/-- The numeral with `n` successors `s` over `z`. -/
def numeral (s : String) (z : Atom) (n : ℕ) : Atom := (unary s).build ⟨List.replicate n (), z⟩

theorem spine_numeral (s : String) {z : Atom} (z_end : (unary s).uncell z = none) (n : ℕ) :
    (unary s).spine (numeral s z n) = ⟨List.replicate n (), z⟩ :=
  (unary s).spine_build_of_canonical z_end

/-- Distinct counts are distinct numerals. -/
theorem numeral_injective (s : String) {z : Atom} (z_end : (unary s).uncell z = none) :
    Function.Injective (numeral s z) := by
  intro n₁ n₂ same
  have := congrArg (fun t => ((unary s).spine t).elems.length) same
  simpa [spine_numeral s z_end] using this

/-- Addition by its two authored equations, `(plus z $m) = $m` and
`(plus (s $n) $m) = (s (plus $n $m))`; an argument that ends elsewhere stays
an unreduced call. -/
def plus (s : String) (z : Atom) (m : Atom) : Atom → Atom :=
  (unary s).recurse (fun u r => (unary s).cell u r)
    (fun e => if e = z then m else .expression [.symbol "plus", e, m])

/-- **Addition of numerals is addition of counts.** -/
theorem plus_numeral (s : String) {z : Atom} (z_end : (unary s).uncell z = none) (n k : ℕ) :
    plus s z (numeral s z k) (numeral s z n) = numeral s z (n + k) := by
  rw [plus, Family.recurse_cell, spine_numeral s z_end, if_pos rfl, numeral, numeral,
    Family.build_append, List.replicate_add]

/-! ### Printing -/

/-- **A spine prints in one walk**: an opening for each cell with its fields,
the end, then one closing parenthesis per cell. This is HE's printed form of
the nested term. -/
theorem print_build (c : String) (m : ℕ) (s : Spine Atom (Fields m)) :
    CoreList.heTokens ((last c m).build s) =
      (s.elems.map fun fs => "(" :: c :: (fs.1.map CoreList.heTokens).flatten).flatten ++
        CoreList.heTokens s.stop ++ List.replicate s.elems.length ")" := by
  obtain ⟨fs, e⟩ := s
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [Family.build_cons, last, CoreList.heTokens, CoreList.heTokensList_eq,
        List.map_cons, List.map_append, List.flatten_cons, List.flatten_append, List.map_nil,
        List.flatten_nil, List.length_cons, List.replicate_succ'] at ih ⊢
      rw [ih]
      simp

end HE

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MeTTa.OSLFCore
open Family

/-- A user's own list: `(Cons $head $tail)` ending in `Nil`. -/
abbrev consNil : CoreList.Manifestation Atom := (binary "Cons").manifestation (.symbol "Nil")

/-- The grammar's entries: `(bnf-v1:entries-cons $head $tail)` ending in
`(bnf-v1:entries-nil)`. -/
abbrev entries : CoreList.Manifestation Atom :=
  (binary "bnf-v1:entries-cons").manifestation (.expression [.symbol "bnf-v1:entries-nil"])

theorem cons_nil_contract : CoreList.Contract consNil := (binary "Cons").contract _ rfl

theorem entries_contract : CoreList.Contract entries :=
  (binary "bnf-v1:entries-cons").contract _ rfl

/-- The written form is the authored one. -/
theorem cons_nil_write :
    consNil.write [.symbol "a", .symbol "b"] =
      .expression [.symbol "Cons", .symbol "a",
        .expression [.symbol "Cons", .symbol "b", .symbol "Nil"]] := rfl

/-- A user list and HE's expression of the same elements agree on length,
indexing and head. -/
theorem user_list_agrees_with_expression (xs : List Atom) :
    consNil.length (consNil.write xs) = CoreList.he.length (CoreList.he.write xs) ∧
      (∀ i, consNil.nth (consNil.write xs) i = xs[i]? ∧
        CoreList.he.nth (CoreList.he.write xs) i = xs[i]?) ∧
      consNil.head (consNil.write xs) = xs.head? ∧
      CoreList.he.head (CoreList.he.write xs) = xs.head? := by
  simpa using CoreList.Contract.agree cons_nil_contract CoreList.he_contract id id xs

/-- **Erasing the family identifies distinct terms.** Both terms read as the
core list `[a]`, yet they differ, so a native list must keep its family. -/
theorem family_erasure_identifies :
    consNil.read (consNil.write [.symbol "a"]) = entries.read (entries.write [.symbol "a"]) ∧
      consNil.write [.symbol "a"] ≠ entries.write [.symbol "a"] := by
  refine ⟨by rw [cons_nil_contract.read_write, entries_contract.read_write], ?_⟩
  intro same
  have := congrArg (fun t => (binary "Cons").uncell t) same
  revert this
  decide

/-- **Spines that are not maximal denote one term twice.** -/
theorem noncanonical_spines :
    (binary "Cons").build ⟨[.symbol "a"], (binary "Cons").cell (.symbol "b") (.symbol "Nil")⟩ =
        (binary "Cons").build ⟨[.symbol "a", .symbol "b"], .symbol "Nil"⟩ ∧
      (⟨[.symbol "a"], (binary "Cons").cell (.symbol "b") (.symbol "Nil")⟩ : Spine Atom Atom) ≠
        ⟨[.symbol "a", .symbol "b"], .symbol "Nil"⟩ := by
  refine ⟨rfl, fun same => ?_⟩
  have := congrArg (fun s : Spine Atom Atom => s.elems.length) same
  simp at this

/-- **An end whose head is a variable can become a cell.** `($h b Nil)` is no
cell; binding `$h` to `Cons` makes it one, so a substituted spine is
re-examined at its end even when the end is not a variable. -/
theorem variable_head_becomes_cell :
    (binary "Cons").uncell (.expression [.var "h", .symbol "b", .symbol "Nil"]) = none ∧
      (binary "Cons").uncell
          (substitute (fun v => if v = "h" then some (.symbol "Cons") else none)
            (.expression [.var "h", .symbol "b", .symbol "Nil"])) =
        some (.symbol "b", .symbol "Nil") := by
  constructor
  · decide
  · decide

/-- **An end that is a cell breaks the contract**: with `(Cons a Nil)` as the
end, the empty list does not read back. -/
theorem cell_end_breaks_contract :
    ¬ CoreList.Contract ((binary "Cons").manifestation
      ((binary "Cons").cell (.symbol "a") (.symbol "Nil"))) := by
  intro contract
  have := contract.read_write []
  have chain : (binary "Cons").spine ((binary "Cons").cell (.symbol "a") (.symbol "Nil")) =
      ⟨[.symbol "a"], .symbol "Nil"⟩ := by
    rw [spine_cell, (binary "Cons").spine_of_none (t := .symbol "Nil") rfl]
  change (binary "Cons").read ((binary "Cons").cell (.symbol "a") (.symbol "Nil"))
    ((binary "Cons").cell (.symbol "a") (.symbol "Nil")) = some [] at this
  unfold Family.read at this
  rw [chain] at this
  revert this
  decide

/-- **A bounded count identifies distinct numerals**: residues modulo any
bound `k` cannot tell the numeral `k` from zero. -/
theorem bounded_numerals_collide (k : ℕ) (positive : 0 < k) :
    numeral "S" (.symbol "Z") k ≠ numeral "S" (.symbol "Z") 0 ∧ k % k = 0 % k := by
  refine ⟨fun same => ?_, by simp⟩
  have := numeral_injective "S" (z := .symbol "Z") rfl same
  omega

/-- `2 + 3 = 5` on Peano numerals, through the law. -/
theorem two_plus_three :
    plus "S" (.symbol "Z") (numeral "S" (.symbol "Z") 3) (numeral "S" (.symbol "Z") 2) =
      numeral "S" (.symbol "Z") 5 :=
  plus_numeral "S" rfl 2 3

/-- Two constructors with disjoint cells, one assignment of recursive positions. -/
def mixed : Family Atom (Atom ⊕ Atom) :=
  (binary "ConsA").sum (binary "ConsB")
    (fun {t f r} h => by
      have := (binary "ConsA").cell_uncell h
      subst this
      simp [binary, reindex, last, lastUncell, lastArgs])
    rfl

/-- **A chain mixing two constructors is one spine** of their sum. -/
theorem mixed_chain :
    mixed.spine (.expression [.symbol "ConsA", .symbol "x",
        .expression [.symbol "ConsB", .symbol "y", .symbol "Nil"]]) =
      ⟨[.inl (.symbol "x"), .inr (.symbol "y")], .symbol "Nil"⟩ := by
  have : (.expression [.symbol "ConsA", .symbol "x",
      .expression [.symbol "ConsB", .symbol "y", .symbol "Nil"]] : Atom) =
      mixed.build ⟨[.inl (.symbol "x"), .inr (.symbol "y")], .symbol "Nil"⟩ := rfl
  rw [this]
  exact mixed.spine_build_of_canonical
    (s := ⟨[.inl (.symbol "x"), .inr (.symbol "y")], .symbol "Nil"⟩) rfl

/-- Binary trees `(Node l k r)` followed through their right child. -/
abbrev rightSpine : Family Atom (Fields 2) := last "Node" 2

/-- **A tree's spine is not its size.** The tree with nodes `1` and `2`, the
second in the left child, has one cell on its right spine; its left child is
a field. -/
theorem tree_spine_is_not_size :
    (rightSpine.spine (.expression [.symbol "Node",
        .expression [.symbol "Node", .symbol "Leaf", .symbol "2", .symbol "Leaf"],
        .symbol "1", .symbol "Leaf"])).elems.length = 1 := by
  have : (.expression [.symbol "Node",
      .expression [.symbol "Node", .symbol "Leaf", .symbol "2", .symbol "Leaf"],
      .symbol "1", .symbol "Leaf"] : Atom) =
      rightSpine.build ⟨[⟨[.expression [.symbol "Node", .symbol "Leaf", .symbol "2", .symbol "Leaf"],
        .symbol "1"], rfl⟩], .symbol "Leaf"⟩ := rfl
  rw [this, rightSpine.spine_build_of_canonical (s := ⟨_, .symbol "Leaf"⟩) rfl]
  rfl

/-- The keys of a search tree `(Node l k r)` in order. -/
def keys : Atom → List Atom
  | .expression [.symbol "Node", l, k, r] => keys l ++ [k] ++ keys r
  | _ => []

/-- A pattern a program can test: the left child is a leaf. -/
def leftIsLeaf : Atom → Bool
  | .expression [.symbol "Node", .symbol "Leaf", _, _] => true
  | _ => false

/-- **Trees read as finite maps identify terms a pattern distinguishes.** Two
search trees hold the keys `1 2`, so a map presentation stores them alike,
yet `(Node Leaf $k $r)` matches only the first. -/
theorem trees_as_maps :
    let leaf : Atom := .symbol "Leaf"
    let first : Atom := .expression [.symbol "Node", leaf, .symbol "1",
      .expression [.symbol "Node", leaf, .symbol "2", leaf]]
    let second : Atom := .expression [.symbol "Node",
      .expression [.symbol "Node", leaf, .symbol "1", leaf], .symbol "2", leaf]
    keys first = keys second ∧ first ≠ second ∧ leftIsLeaf first ≠ leftIsLeaf second := by
  intro leaf first second
  refine ⟨by simp [first, second, leaf, keys], by decide, by decide⟩

/-- **Lists read as bags identify terms a pattern distinguishes.** `[a b]` and
`[b a]` have one bag of elements, and different heads. -/
theorem lists_as_bags :
    ((([.symbol "a", .symbol "b"] : List Atom) : Multiset Atom) =
        (([.symbol "b", .symbol "a"] : List Atom) : Multiset Atom)) ∧
      consNil.head (consNil.write [.symbol "a", .symbol "b"]) ≠
        consNil.head (consNil.write [.symbol "b", .symbol "a"]) := by
  refine ⟨Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _), ?_⟩
  rw [cons_nil_contract.head_write, cons_nil_contract.head_write]
  decide

/-- **A fold into bags is invariant under reordering.** `match'` answers each
element and adds the answers of the rest; on a list ending in `Nil` this is
the sum of the elements' answers, so reordering the elements does not change
it. -/
theorem bag_fold_reorders {β : Type} (answers : Atom → Multiset β) {xs ys : List Atom}
    (reordered : xs.Perm ys) :
    (binary "Cons").recurse (fun x acc => answers x + acc) (fun _ => 0)
        (consNil.write xs) =
      (binary "Cons").recurse (fun x acc => answers x + acc) (fun _ => 0)
        (consNil.write ys) := by
  have sum : ∀ zs : List Atom, (binary "Cons").recurse (fun x acc => answers x + acc) (fun _ => 0)
      (consNil.write zs) = (zs.map answers).sum := by
    intro zs
    rw [recurse_eq_foldr]
    change List.foldr _ _ ((binary "Cons").spine ((binary "Cons").build ⟨zs, _⟩)).elems = _
    rw [(binary "Cons").spine_build_of_canonical (s := ⟨zs, .symbol "Nil"⟩) rfl]
    induction zs with
    | nil => rfl
    | cons z zs ih => simp [ih]
  rw [sum, sum]
  exact (reordered.map answers).sum_eq

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.Presentations
