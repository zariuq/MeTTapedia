import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Occupancy
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm
import Mettapedia.GSLT.Logic.SpatialCharacteristic

/-!
# Hereditary structural congruence

`Cong` closes the monoid laws of parallel composition under parallel
composition and nothing else: two atoms are congruent only when they are the
same atom.  So `kk (par nil nil)` and `kk nil` are not congruent, although the
processes they quote are.  That is the relation reduction matches subjects up
to, and the relation the soup theorem is about.

A formula that recognizes a process by its constructor structure descends into
quoted arguments — an argument formula recognizes an argument — so what such a
formula characterizes is the congruence that *also* closes under every
constructor's arguments.  This module defines that relation, `HCong`, proves it
strictly contains `Cong`, and proves the theorem the characteristic formulas
will rest on: two processes are hereditarily congruent exactly when their
component bags match atom for atom, with matching atoms of one shape whose
arguments are hereditarily congruent.

The thirteen constructor congruences are one rule, stated through the shape
and argument view of an atom: an atom is its shape applied to its arguments,
and `rebuild` witnesses that the view loses nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.GSLT.SpatialCharacteristic

/-! ## The shape and argument view -/

/-- The shape of an atom; the empty process and a parallel composition have
none. -/
def shapeOf : Comb → Option Shape
  | mm _ _ => some .mm
  | dd _ _ _ => some .dd
  | kk _ => some .kk
  | fw _ _ => some .fw
  | bl _ _ => some .bl
  | br _ _ => some .br
  | sy _ _ _ => some .sy
  | ev _ => some .ev
  | qq _ _ => some .qq
  | consPar _ _ _ => some .consPar
  | consMsg _ _ _ => some .consMsg
  | consDup _ _ _ _ => some .consDup
  | consSyn _ _ _ _ => some .consSyn
  | nil => none
  | par _ _ => none

/-- The arguments of an atom, in order.  Every argument is a name, hence a
process, except the payload of `qq`, which is a process outright. -/
def args : Comb → List Comb
  | mm a b => [a, b]
  | dd a b c => [a, b, c]
  | kk a => [a]
  | fw a b => [a, b]
  | bl a b => [a, b]
  | br a b => [a, b]
  | sy a b c => [a, b, c]
  | ev a => [a]
  | qq a p => [a, p]
  | consPar a b c => [a, b, c]
  | consMsg a b c => [a, b, c]
  | consDup a b c e => [a, b, c, e]
  | consSyn a b c e => [a, b, c, e]
  | nil => []
  | par _ _ => []

/-- An atom from a shape and arguments of the right arity. -/
def rebuild : Shape → List Comb → Option Comb
  | .mm, [a, b] => some (mm a b)
  | .dd, [a, b, c] => some (dd a b c)
  | .kk, [a] => some (kk a)
  | .fw, [a, b] => some (fw a b)
  | .bl, [a, b] => some (bl a b)
  | .br, [a, b] => some (br a b)
  | .sy, [a, b, c] => some (sy a b c)
  | .ev, [a] => some (ev a)
  | .qq, [a, p] => some (qq a p)
  | .consPar, [a, b, c] => some (consPar a b c)
  | .consMsg, [a, b, c] => some (consMsg a b c)
  | .consDup, [a, b, c, e] => some (consDup a b c e)
  | .consSyn, [a, b, c, e] => some (consSyn a b c e)
  | _, _ => none

/-- The view loses nothing: an atom is rebuilt from its shape and arguments. -/
theorem rebuild_shape_args {a : Comb} {s : Shape} (h : shapeOf a = some s) :
    rebuild s (args a) = some a := by
  cases a <;> simp only [shapeOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- Atoms of one shape with equal arguments are equal. -/
theorem eq_of_shape_args {a b : Comb} {s : Shape} (ha : shapeOf a = some s)
    (hb : shapeOf b = some s) (hargs : args a = args b) : a = b := by
  have := rebuild_shape_args ha
  rw [hargs, rebuild_shape_args hb] at this
  exact (Option.some.inj this).symm

theorem components_atom {a : Comb} {s : Shape} (h : shapeOf a = some s) :
    components a = {a} := by
  rw [components_eq_coe]
  cases a <;> simp_all [shapeOf, componentList]

/-- Every component of a term is an atom. -/
theorem shape_of_mem_componentList {t x : Comb} (hx : x ∈ componentList t) :
    ∃ s, shapeOf x = some s := by
  induction t with
  | par p q ihp ihq =>
      simp only [componentList, List.mem_append] at hx
      exact hx.elim ihp ihq
  | nil => simp [componentList] at hx
  | _ => simp_all [componentList, shapeOf]

theorem shape_of_mem_components {t x : Comb} (hx : x ∈ components t) :
    ∃ s, shapeOf x = some s :=
  shape_of_mem_componentList (by rwa [components_eq_coe, Multiset.mem_coe] at hx)

/-! ## The hereditary congruence -/

mutual

/-- **Hereditary structural congruence.**  The monoid laws of parallel
composition, closed under parallel composition and under every constructor's
arguments.  The last rule is the thirteen constructor congruences at once: two
atoms of one shape whose arguments are pairwise congruent. -/
inductive HCong : Comb → Comb → Prop where
  | refl (p : Comb) : HCong p p
  | symm {p q : Comb} : HCong p q → HCong q p
  | trans {p q r : Comb} : HCong p q → HCong q r → HCong p r
  | parNil (p : Comb) : HCong (par p nil) p
  | parComm (p q : Comb) : HCong (par p q) (par q p)
  | parAssoc (p q r : Comb) : HCong (par (par p q) r) (par p (par q r))
  | parLeft (q : Comb) {p p' : Comb} : HCong p p' → HCong (par p q) (par p' q)
  | parRight (p : Comb) {q q' : Comb} : HCong q q' → HCong (par p q) (par p q')
  | atom {a b : Comb} {s : Shape} : shapeOf a = some s → shapeOf b = some s →
      HCongArgs (args a) (args b) → HCong a b

/-- Pairwise hereditary congruence of argument lists. -/
inductive HCongArgs : List Comb → List Comb → Prop where
  | nil : HCongArgs [] []
  | cons {x y : Comb} {xs ys : List Comb} :
      HCong x y → HCongArgs xs ys → HCongArgs (x :: xs) (y :: ys)

end

theorem HCongArgs.refl : ∀ (l : List Comb), HCongArgs l l
  | [] => .nil
  | x :: xs => .cons (.refl x) (HCongArgs.refl xs)

theorem HCongArgs.symm : ∀ {xs ys : List Comb}, HCongArgs xs ys → HCongArgs ys xs
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons h.symm rest.symm

theorem HCongArgs.trans : ∀ {xs ys zs : List Comb},
    HCongArgs xs ys → HCongArgs ys zs → HCongArgs xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ r₁, .cons h₂ r₂ => .cons (h₁.trans h₂) (r₁.trans r₂)

theorem HCongArgs.forall₂ : ∀ {xs ys : List Comb}, HCongArgs xs ys → List.Forall₂ HCong xs ys
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons h rest.forall₂

theorem HCongArgs.of_forall₂ {xs ys : List Comb} (h : List.Forall₂ HCong xs ys) :
    HCongArgs xs ys := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

/-- The shallow congruence is contained in the hereditary one. -/
theorem HCong.ofCong {p q : Comb} (h : Cong p q) : HCong p q := by
  induction h with
  | refl p => exact .refl p
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => exact .parNil p
  | parComm p q => exact .parComm p q
  | parAssoc p q r => exact .parAssoc p q r
  | parLeft q _ ih => exact .parLeft q ih
  | parRight p _ ih => exact .parRight p ih

/-! ## The containment is strict

A discarder listening at the quotation of `par nil nil` and one listening at
the quotation of `nil` are hereditarily congruent — the quoted processes are
congruent — but not congruent: `Cong` never looks inside an atom, and the
names a term carries are a `Cong` invariant. -/

theorem hcong_quoted_unit : HCong (kk (par nil nil)) (kk nil) :=
  .atom rfl rfl (.cons (.parNil nil) .nil)

theorem not_cong_quoted_unit : ¬ Cong (kk (par nil nil)) (kk nil) := by
  intro h
  have hnames := cong_names h
  have mem : par nil nil ∈ names (kk (par nil nil)) := by simp [names]
  rw [hnames] at mem
  simp [names] at mem

/-! ## Atoms match atom for atom -/

/-- Two atoms of one shape whose arguments are hereditarily congruent. -/
def HAtom (a b : Comb) : Prop :=
  ∃ s, shapeOf a = some s ∧ shapeOf b = some s ∧ HCongArgs (args a) (args b)

theorem HAtom.hcong {a b : Comb} (h : HAtom a b) : HCong a b :=
  let ⟨_, ha, hb, hargs⟩ := h
  .atom ha hb hargs

theorem HAtom.refl_of_shape {a : Comb} {s : Shape} (h : shapeOf a = some s) : HAtom a a :=
  ⟨s, h, h, HCongArgs.refl _⟩

instance : Std.Symm HAtom where
  symm _ _ h :=
    let ⟨s, ha, hb, hargs⟩ := h
    ⟨s, hb, ha, hargs.symm⟩

instance : IsTrans Comb HAtom where
  trans _ _ _ h₁ h₂ := by
    obtain ⟨s, ha, hb, hargs₁⟩ := h₁
    obtain ⟨s', hb', hc, hargs₂⟩ := h₂
    cases Option.some.inj (hb.symm.trans hb')
    exact ⟨s, ha, hc, hargs₁.trans hargs₂⟩

/-- The component bag of a term is related to itself, atom for atom. -/
theorem rel_hatom_refl (t : Comb) : Multiset.Rel HAtom (components t) (components t) :=
  Multiset.rel_refl_of_refl_on fun _ hx =>
    let ⟨_, hs⟩ := shape_of_mem_components hx
    HAtom.refl_of_shape hs

theorem components_par (p q : Comb) : components (par p q) = components p + components q := by
  rw [components_eq_coe, components_eq_coe, components_eq_coe]
  simp only [componentList]
  exact (Multiset.coe_add _ _).symm

theorem components_nil_eq : components nil = 0 := by
  rw [components_eq_coe]; rfl

/-- **Hereditary congruence matches component bags atom for atom.** -/
theorem HCong.rel : ∀ {p q : Comb}, HCong p q →
    Multiset.Rel HAtom (components p) (components q)
  | _, _, .refl p => rel_hatom_refl p
  | _, _, .symm h => rel_symm h.rel
  | _, _, .trans h₁ h₂ => Multiset.Rel.trans HAtom h₁.rel h₂.rel
  | _, _, .parNil p => by
      have e : components (par p nil) = components p := by
        rw [components_par, components_nil_eq, add_zero]
      rw [e]; exact rel_hatom_refl p
  | _, _, .parComm p q => by
      have e : components (par p q) = components (par q p) := by
        rw [components_par, components_par, add_comm]
      rw [e]; exact rel_hatom_refl _
  | _, _, .parAssoc p q r => by
      have e : components (par (par p q) r) = components (par p (par q r)) := by
        rw [components_par, components_par, components_par, components_par, add_assoc]
      rw [e]; exact rel_hatom_refl _
  | _, _, .parLeft q h => by
      rw [components_par, components_par]
      exact Multiset.Rel.add h.rel (rel_hatom_refl q)
  | _, _, .parRight p h => by
      rw [components_par, components_par]
      exact Multiset.Rel.add (rel_hatom_refl p) h.rel
  | _, _, .atom ha hb hargs => by
      rw [components_atom ha, components_atom hb]
      exact .cons ⟨_, ha, hb, hargs⟩ .zero

/-- Two lists whose bags match atom for atom compose to hereditarily congruent
terms. -/
theorem hcong_ofList_of_rel : ∀ (l₁ l₂ : List Comb),
    Multiset.Rel HAtom (↑l₁) (↑l₂) → HCong (ofList l₁) (ofList l₂)
  | [], l₂, h => by
      rw [Multiset.coe_nil, Multiset.rel_zero_left, Multiset.coe_eq_zero] at h
      rw [h]
      exact .refl _
  | a :: l₁, l₂, h => by
      rw [← Multiset.cons_coe, Multiset.rel_cons_left] at h
      obtain ⟨b, rest, hab, hrest, hl₂⟩ := h
      obtain ⟨l', hl'⟩ := Quot.exists_rep rest
      have hl'' : (↑l' : Multiset Comb) = rest := hl'
      rw [← hl''] at hl₂ hrest
      rw [Multiset.cons_coe, Multiset.coe_eq_coe] at hl₂
      have perm : HCong (ofList l₂) (ofList (b :: l')) := .ofCong (ofList_perm hl₂)
      have head : HCong (ofList (a :: l₁)) (ofList (b :: l')) := by
        simp only [ofList]
        exact .trans (.parLeft _ hab.hcong) (.parRight _ (hcong_ofList_of_rel l₁ l' hrest))
      exact head.trans perm.symm

/-- **Terms whose component bags match atom for atom are hereditarily
congruent.** -/
theorem HCong.of_rel {p q : Comb} (h : Multiset.Rel HAtom (components p) (components q)) :
    HCong p q := by
  rw [components_eq_coe, components_eq_coe] at h
  exact (HCong.ofCong (cong_ofList p)).trans
    ((hcong_ofList_of_rel _ _ h).trans (HCong.ofCong (cong_ofList q)).symm)

/-- **The hereditary soup theorem.**  Hereditary congruence is matching of
component bags atom for atom, where atoms match when they have one shape and
hereditarily congruent arguments. -/
theorem hcong_iff_rel (p q : Comb) :
    HCong p q ↔ Multiset.Rel HAtom (components p) (components q) :=
  ⟨HCong.rel, HCong.of_rel⟩

/-- On atoms, hereditary congruence is the atom relation.  Both sides must be
atoms: `par x nil` is hereditarily congruent to the atom `x` without being one. -/
theorem hatom_iff_hcong {a b : Comb} {s s' : Shape} (ha : shapeOf a = some s)
    (hb : shapeOf b = some s') : HAtom a b ↔ HCong a b := by
  constructor
  · exact HAtom.hcong
  · intro h
    have := h.rel
    rw [components_atom ha, components_atom hb, rel_singleton_iff] at this
    obtain ⟨t, ht, hat⟩ := this
    cases Multiset.singleton_inj.mp ht
    exact hat

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.hcong_iff_rel
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.not_cong_quoted_unit
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.hcong_quoted_unit
