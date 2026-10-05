import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Order.Defs.Unbundled
import Mettapedia.GSLT.Logic.SeparationAlgebra

/-!
# Spatial formulas over an atomic soup

A soup presentation decomposes a term into a bag of atoms, and identifies terms
whose bags agree.  This module gives such a carrier a spatial logic: formulas
that name the empty bag, split a bag into two parts, and recognize a single atom
by its shape together with formulas for its arguments.

The composition connective is read on bags, never on positions.  A bag splits
into two sub-bags with no order between them, which is what makes the
connective a separating conjunction rather than a concatenation.  Bags under sum
are a separation algebra in which every two bags are separate, and the
composition connective *is* that algebra's separating conjunction
(`sat_sep_eq_sepConj`), with the empty-bag formula its unit (`sat_nil_eq_emp`).
Symmetry, associativity and the unit law of composition are therefore the
algebra's laws, read through that identity (`sat_sep_comm`, `sat_sep_assoc`,
`sat_sep_nil`), and never have to be proved again for a particular carrier.

An atom's arguments are again terms, so the logic descends into them.  This is
what lets a formula built from a term recognize that term *hereditarily*: a
term is recognized when its bag of atoms matches the formula's atoms one for
one, and each argument in turn is recognized by the corresponding argument
formula.  The relation this characterizes is therefore the congruence closed
under argument positions, which is stronger than the congruence closed under
parallel composition alone; a carrier instantiating this module has to say
which relation it means.

Nothing here is about any particular calculus.  A calculus supplies the shapes
of its atoms, the arguments of an atom, and the bag of a term.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.SpatialCharacteristic

universe u v

/-- Spatial formulas over an alphabet of atom shapes. -/
inductive Formula (Shape : Type u) : Type u where
  /-- The empty bag. -/
  | nil
  /-- Every bag. -/
  | top
  /-- A bag that splits into two parts satisfying the two formulas. -/
  | sep (left right : Formula Shape)
  | and (left right : Formula Shape)
  | or (left right : Formula Shape)
  /-- A bag holding one atom of the given shape, whose arguments satisfy the
  argument formulas. -/
  | atom (shape : Shape) (arguments : List (Formula Shape))

/-- What a carrier supplies: the bag of atoms of a term, the shape of an atom,
and the arguments of an atom.  Terms that are not atoms have no shape. -/
structure AtomicSoup (Term : Type v) (Shape : Type u) where
  components : Term → Multiset Term
  shapeOf : Term → Option Shape
  args : Term → List Term

variable {Term : Type v} {Shape : Type u}

mutual

/-- Satisfaction of a formula by a bag.  The split clause takes the bag as a
sum, with no order between the summands. -/
inductive Sat (S : AtomicSoup Term Shape) : Formula Shape → Multiset Term → Prop where
  | nil : Sat S .nil 0
  | top (bag : Multiset Term) : Sat S .top bag
  | sep {left right : Formula Shape} {first second : Multiset Term} :
      Sat S left first → Sat S right second → Sat S (.sep left right) (first + second)
  | and {left right : Formula Shape} {bag : Multiset Term} :
      Sat S left bag → Sat S right bag → Sat S (.and left right) bag
  | orLeft {left right : Formula Shape} {bag : Multiset Term} :
      Sat S left bag → Sat S (.or left right) bag
  | orRight {left right : Formula Shape} {bag : Multiset Term} :
      Sat S right bag → Sat S (.or left right) bag
  | atom {shape : Shape} {arguments : List (Formula Shape)} {a : Term} :
      S.shapeOf a = some shape → SatArgs S arguments (S.args a) →
      Sat S (.atom shape arguments) {a}

/-- Pointwise satisfaction of argument formulas by argument terms, each
argument read as its own bag. -/
inductive SatArgs (S : AtomicSoup Term Shape) : List (Formula Shape) → List Term → Prop where
  | nil : SatArgs S [] []
  | cons {formula : Formula Shape} {formulas : List (Formula Shape)} {x : Term} {xs : List Term} :
      Sat S formula (S.components x) → SatArgs S formulas xs →
      SatArgs S (formula :: formulas) (x :: xs)

end

variable {S : AtomicSoup Term Shape}

/-! ## Inversion -/

theorem sat_nil_iff {bag : Multiset Term} : Sat S .nil bag ↔ bag = 0 := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem sat_top {bag : Multiset Term} : Sat S .top bag := .top bag

theorem sat_sep_iff {left right : Formula Shape} {bag : Multiset Term} :
    Sat S (.sep left right) bag ↔
      ∃ first second, bag = first + second ∧ Sat S left first ∧ Sat S right second := by
  constructor
  · intro h; cases h with
    | sep hl hr => exact ⟨_, _, rfl, hl, hr⟩
  · rintro ⟨first, second, rfl, hl, hr⟩; exact .sep hl hr

theorem sat_and_iff {left right : Formula Shape} {bag : Multiset Term} :
    Sat S (.and left right) bag ↔ Sat S left bag ∧ Sat S right bag := by
  constructor
  · intro h; cases h with
    | and hl hr => exact ⟨hl, hr⟩
  · rintro ⟨hl, hr⟩; exact .and hl hr

theorem sat_or_iff {left right : Formula Shape} {bag : Multiset Term} :
    Sat S (.or left right) bag ↔ Sat S left bag ∨ Sat S right bag := by
  constructor
  · intro h; cases h with
    | orLeft hl => exact Or.inl hl
    | orRight hr => exact Or.inr hr
  · rintro (hl | hr)
    · exact .orLeft hl
    · exact .orRight hr

theorem sat_atom_iff {shape : Shape} {arguments : List (Formula Shape)} {bag : Multiset Term} :
    Sat S (.atom shape arguments) bag ↔
      ∃ a, bag = {a} ∧ S.shapeOf a = some shape ∧ SatArgs S arguments (S.args a) := by
  constructor
  · intro h; cases h with
    | atom hs hargs => exact ⟨_, rfl, hs, hargs⟩
  · rintro ⟨a, rfl, hs, hargs⟩; exact .atom hs hargs

/-! ## Composition is the separating conjunction of bags -/

open Mettapedia.GSLT.SeparationAlgebra

/-- The empty-bag formula is the unit of the bag separation algebra. -/
theorem sat_nil_eq_emp : Sat S .nil = emp :=
  funext fun _ => propext sat_nil_iff

/-- **The composition connective is the separating conjunction** of the
separation algebra of bags. -/
theorem sat_sep_eq_sepConj (left right : Formula Shape) :
    Sat S (.sep left right) = (Sat S left ∗ Sat S right) :=
  funext fun _ => propext (sat_sep_iff.trans (sepConj_iff_of_total (fun _ _ => trivial)).symm)

/-- Composition is symmetric: the commutativity of the separating
conjunction. -/
theorem sat_sep_comm (left right : Formula Shape) :
    Sat S (.sep left right) = Sat S (.sep right left) := by
  rw [sat_sep_eq_sepConj, sat_sep_eq_sepConj, sepConj_comm]

/-- Composition is associative. -/
theorem sat_sep_assoc (first second third : Formula Shape) :
    Sat S (.sep (.sep first second) third) = Sat S (.sep first (.sep second third)) := by
  simp only [sat_sep_eq_sepConj, sepConj_assoc]

/-- The empty-bag formula is a unit for composition. -/
theorem sat_sep_nil (formula : Formula Shape) :
    Sat S (.sep formula .nil) = Sat S formula := by
  rw [sat_sep_eq_sepConj, sat_nil_eq_emp, sepConj_emp]

/-- Argument satisfaction is pointwise; stated by recursion on the derivation,
since the derivations are mutually inductive. -/
theorem SatArgs.forall₂ : ∀ {formulas : List (Formula Shape)} {xs : List Term},
    SatArgs S formulas xs →
      List.Forall₂ (fun formula x => Sat S formula (S.components x)) formulas xs
  | _, _, .nil => .nil
  | _, _, .cons hx rest => .cons hx rest.forall₂

theorem SatArgs.of_forall₂ {formulas : List (Formula Shape)} {xs : List Term}
    (h : List.Forall₂ (fun formula x => Sat S formula (S.components x)) formulas xs) :
    SatArgs S formulas xs := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons hx ih

theorem satArgs_iff_forall₂ {formulas : List (Formula Shape)} {xs : List Term} :
    SatArgs S formulas xs ↔
      List.Forall₂ (fun formula x => Sat S formula (S.components x)) formulas xs :=
  ⟨SatArgs.forall₂, SatArgs.of_forall₂⟩

/-! ## The bag relation lemmas the exactness theorems rest on

`Multiset.Rel r` pairs the atoms of two bags one for one under `r`.  When `r`
is an equivalence, any pairing of one atom may be exchanged for any other
equivalent one, which is what lets a checker match atoms greedily. -/

theorem rel_singleton_iff {r : Term → Term → Prop} {a : Term} {bag : Multiset Term} :
    Multiset.Rel r {a} bag ↔ ∃ b, bag = {b} ∧ r a b := by
  rw [← Multiset.cons_zero, Multiset.rel_cons_left]
  constructor
  · rintro ⟨b, rest, hab, hrest, rfl⟩
    rw [Multiset.rel_zero_left] at hrest
    exact ⟨b, by rw [hrest, Multiset.cons_zero], hab⟩
  · rintro ⟨b, rfl, hab⟩
    exact ⟨b, 0, hab, .zero, (Multiset.cons_zero b).symm⟩

theorem rel_symm {r : Term → Term → Prop} [Std.Symm r] {s t : Multiset Term}
    (h : Multiset.Rel r s t) : Multiset.Rel r t s := by
  induction h with
  | zero => exact .zero
  | cons hab _ ih => exact .cons (Std.Symm.symm _ _ hab) ih

theorem rel_refl {r : Term → Term → Prop} [Std.Refl r] (s : Multiset Term) :
    Multiset.Rel r s s :=
  Multiset.rel_refl_of_refl_on fun x _ => Std.Refl.refl x

/-- **Greedy exchange.**  If a bag with `a` in front is related to `bs`, then
removing any `b ∈ bs` equivalent to `a` leaves the rest related. -/
theorem rel_erase_of_mem {r : Term → Term → Prop} [Std.Symm r] [IsTrans Term r]
    [DecidableEq Term] {a b : Term} {as bs : Multiset Term}
    (h : Multiset.Rel r (a ::ₘ as) bs) (hb : b ∈ bs) (hab : r a b) :
    Multiset.Rel r as (bs.erase b) := by
  rw [Multiset.rel_cons_left] at h
  obtain ⟨b', rest, hab', hrest, rfl⟩ := h
  by_cases hbb : b = b'
  · subst hbb
    rw [Multiset.erase_cons_head]
    exact hrest
  · have hb_rest : b ∈ rest := by
      rw [Multiset.mem_cons] at hb
      exact hb.resolve_left hbb
    rw [Multiset.erase_cons_tail _ (Ne.symm hbb)]
    have hrest' : Multiset.Rel r as (b ::ₘ rest.erase b) := by
      rwa [Multiset.cons_erase hb_rest]
    rw [Multiset.rel_cons_right] at hrest'
    obtain ⟨a', as', ha'b, has', rfl⟩ := hrest'
    have ha'b' : r a' b' :=
      IsTrans.trans _ _ _ ha'b (IsTrans.trans _ _ _ (Std.Symm.symm _ _ hab) hab')
    exact .cons ha'b' has'


/-! ## Deciding the bag relation for an equivalence

When the atom relation is an equivalence, a bag relation can be decided by
matching greedily: pair the first atom with any atom the decision accepts and
continue on what is left.  Greedy exchange is what licenses taking the first
acceptable match instead of searching. -/

section Greedy

variable [DecidableEq Term]

/-- Greedy matching of two lists under a decision on atoms. -/
def greedy (dec : Term → Term → Bool) : List Term → List Term → Bool
  | [], bs => bs.isEmpty
  | a :: as, bs =>
    match bs.find? (fun b => dec a b) with
    | none => false
    | some b => greedy dec as (bs.erase b)

/-- **Greedy matching decides the bag relation**, for an equivalence, whenever
the decision agrees with the relation on the atoms present. -/
theorem greedy_eq_true_iff {r : Term → Term → Prop} [Std.Symm r] [IsTrans Term r]
    (dec : Term → Term → Bool) :
    ∀ (as bs : List Term), (∀ a ∈ as, ∀ b ∈ bs, (dec a b = true ↔ r a b)) →
      (greedy dec as bs = true ↔ Multiset.Rel r (↑as) (↑bs))
  | [], bs, _ => by
      simp only [greedy, List.isEmpty_iff, Multiset.coe_nil, Multiset.rel_zero_left,
        Multiset.coe_eq_zero]
  | a :: as, bs, spec => by
      simp only [greedy]
      cases found : bs.find? (fun b => dec a b) with
      | none =>
          simp only [Bool.false_eq_true, false_iff]
          intro h
          rw [← Multiset.cons_coe, Multiset.rel_cons_left] at h
          obtain ⟨b, rest, hab, -, hbs⟩ := h
          have hb : b ∈ bs := by
            have : b ∈ (↑bs : Multiset Term) := by rw [hbs]; exact Multiset.mem_cons_self b rest
            exact Multiset.mem_coe.mp this
          have := List.find?_eq_none.mp found b hb
          exact this ((spec a List.mem_cons_self b hb).mpr hab)
      | some b =>
          have hdec : dec a b = true := List.find?_some found
          have hb : b ∈ bs := List.mem_of_find?_eq_some found
          have hab : r a b := (spec a List.mem_cons_self b hb).mp hdec
          have spec' : ∀ a' ∈ as, ∀ b' ∈ bs.erase b, (dec a' b' = true ↔ r a' b') :=
            fun a' ha' b' hb' =>
              spec a' (List.mem_cons_of_mem a ha') b' (List.mem_of_mem_erase hb')
          rw [greedy_eq_true_iff dec as (bs.erase b) spec']
          have hbmem : b ∈ (↑bs : Multiset Term) := Multiset.mem_coe.mpr hb
          constructor
          · intro h
            rw [← Multiset.cons_coe, ← Multiset.cons_erase hbmem]
            exact .cons hab h
          · intro h
            rw [← Multiset.cons_coe] at h
            exact rel_erase_of_mem h hbmem hab

end Greedy

end Mettapedia.GSLT.SpatialCharacteristic
