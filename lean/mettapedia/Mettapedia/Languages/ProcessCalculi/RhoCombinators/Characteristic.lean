import Mettapedia.Languages.ProcessCalculi.RhoCombinators.HereditaryCongruence

/-!
# Characteristic spatial formulas for the combinators

Every process has a formula, built from its syntax, that recognizes exactly the
processes hereditarily congruent to it.  The formula is compositional: the
empty process is the empty bag, a parallel composition is a separating
conjunction, and an atom is its shape applied to the characteristic formulas of
its arguments.  No connective's meaning is the congruence; the congruence is
what falls out of the bag semantics.

**Exactness** (`char_exact`): a process satisfies the characteristic formula of
`p` exactly when it is hereditarily congruent to `p`.  The relation is `HCong`,
not `Cong`: an argument formula recognizes its argument up to congruence, so the
formula cannot tell `kk (par nil nil)` from `kk nil`, and neither does `HCong`.
`Cong` can (`not_cong_quoted_unit`), which is why the characterized relation
had to be settled before the formulas were built.

**Separation**: two processes that are not hereditarily congruent are told apart
by the characteristic formula of the first.

**A checker that runs.**  `charCheck` decides satisfaction by matching component
bags greedily, descending into arguments, with the term's size as fuel;
`charCheck_iff` proves it agrees with satisfaction.  The controls at the end are
settled by the kernel from that checker and transported to satisfaction by the
agreement theorem, so each one is a computation rather than a claim.

The size bound the recursion needs is `Seeds.names_size_lt`: every argument of
an atom is one of its names, hence a strictly smaller term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.GSLT.SpatialCharacteristic

/-- The combinators as an atomic soup: component bags, atom shapes, and atom
arguments. -/
def rhoSoup : AtomicSoup Comb Shape where
  components := components
  shapeOf := shapeOf
  args := args

/-! ## Structural facts the recursion needs -/

theorem shapeOf_eq_none_iff {t : Comb} :
    shapeOf t = none ↔ t = nil ∨ ∃ p q, t = par p q := by
  cases t with
  | nil => simp [shapeOf]
  | par p q => simp only [shapeOf, true_iff]; exact Or.inr ⟨p, q, rfl⟩
  | _ => simp [shapeOf]

/-- Every argument of an atom is one of its names.  With `names_size_lt` this
is the decreasing measure for the recursion below. -/
theorem mem_names_of_mem_args : ∀ (a x : Comb), x ∈ args a → x ∈ names a := by
  intro a x hx
  cases a <;> simp_all [args, names]

theorem size_pos (t : Comb) : 0 < size t := by
  cases t <;> simp only [size] <;> omega

theorem size_le_of_mem_componentList :
    ∀ (t x : Comb), x ∈ componentList t → size x ≤ size t := by
  intro t
  induction t with
  | nil => intro x hx; simp [componentList] at hx
  | par p q ihp ihq =>
      intro x hx
      simp only [componentList, List.mem_append] at hx
      rcases hx with hx | hx
      · have := ihp x hx; simp only [size]; omega
      · have := ihq x hx; simp only [size]; omega
  | _ =>
      intro x hx
      simp only [componentList, List.mem_singleton] at hx
      subst hx
      exact le_refl _

/-! ## The characteristic formula -/

/-- **The characteristic formula of a process**, by structural recursion on its
syntax. -/
def char : Comb → Formula Shape
  | nil => .nil
  | par p q => .sep (char p) (char q)
  | mm a b => .atom .mm [char a, char b]
  | dd a b c => .atom .dd [char a, char b, char c]
  | kk a => .atom .kk [char a]
  | fw a b => .atom .fw [char a, char b]
  | bl a b => .atom .bl [char a, char b]
  | br a b => .atom .br [char a, char b]
  | sy a b c => .atom .sy [char a, char b, char c]
  | ev a => .atom .ev [char a]
  | qq a p => .atom .qq [char a, char p]
  | consPar a b c => .atom .consPar [char a, char b, char c]
  | consMsg a b c => .atom .consMsg [char a, char b, char c]
  | consDup a b c e => .atom .consDup [char a, char b, char c, char e]
  | consSyn a b c e => .atom .consSyn [char a, char b, char c, char e]

/-- On an atom the characteristic formula is the shape applied to the
characteristic formulas of the arguments.  This is the one equation the atom
case of exactness needs, uniformly in the thirteen shapes. -/
theorem char_atom {a : Comb} {s : Shape} (h : shapeOf a = some s) :
    char a = .atom s ((args a).map char) := by
  cases a <;> simp only [shapeOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- Argument formulas recognize an argument list exactly when the lists are
pairwise hereditarily congruent, given exactness at each argument. -/
theorem satArgs_map_char_iff : ∀ (l : List Comb),
    (∀ x ∈ l, ∀ m, Sat rhoSoup (char x) m ↔ Multiset.Rel HAtom (components x) m) →
    ∀ l' : List Comb, (SatArgs rhoSoup (l.map char) l' ↔ HCongArgs l l')
  | [], _, l' => by
      constructor
      · intro h; cases h; exact .nil
      · intro h; cases h; exact .nil
  | x :: l, ih, l' => by
      have ihx := ih x List.mem_cons_self
      have ihl := satArgs_map_char_iff l (fun z hz => ih z (List.mem_cons_of_mem x hz))
      constructor
      · intro h
        cases h with
        | cons hx hrest =>
            exact .cons (HCong.of_rel ((ihx _).mp hx)) ((ihl _).mp hrest)
      · intro h
        cases h with
        | cons hxy hrest =>
            exact .cons ((ihx _).mpr hxy.rel) ((ihl _).mpr hrest)

/-- The atom case of exactness, uniformly in the shape. -/
theorem sat_char_atom_iff {a : Comb} {s : Shape} (hs : shapeOf a = some s)
    (ih : ∀ x ∈ args a, ∀ m, Sat rhoSoup (char x) m ↔ Multiset.Rel HAtom (components x) m)
    (m : Multiset Comb) : Sat rhoSoup (char a) m ↔ Multiset.Rel HAtom (components a) m := by
  rw [char_atom hs, sat_atom_iff, components_atom hs, rel_singleton_iff]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  show shapeOf t = some s ∧ SatArgs rhoSoup ((args a).map char) (args t) ↔ HAtom a t
  rw [satArgs_map_char_iff (args a) ih (args t)]
  constructor
  · rintro ⟨ht, hargs⟩
    exact ⟨s, hs, ht, hargs⟩
  · rintro ⟨s', hs', ht, hargs⟩
    cases Option.some.inj (hs.symm.trans hs')
    exact ⟨ht, hargs⟩

private theorem sat_char_iff_rel_aux : ∀ (n : Nat) (p : Comb), size p ≤ n →
    ∀ (m : Multiset Comb), Sat rhoSoup (char p) m ↔ Multiset.Rel HAtom (components p) m
  | 0, p, hp, _ => absurd hp (by have := size_pos p; omega)
  | n + 1, p, hp, m => by
      cases hs : shapeOf p with
      | none =>
          rcases shapeOf_eq_none_iff.mp hs with rfl | ⟨u, v, rfl⟩
          · rw [char, sat_nil_iff, components_nil_eq, Multiset.rel_zero_left]
          · have hu : size u ≤ n := by
              have := size_pos v; simp only [size] at hp; omega
            have hv : size v ≤ n := by
              have := size_pos u; simp only [size] at hp; omega
            rw [char, sat_sep_iff, components_par, Multiset.rel_add_left]
            constructor
            · rintro ⟨m₁, m₂, rfl, h₁, h₂⟩
              exact ⟨m₁, m₂, (sat_char_iff_rel_aux n u hu m₁).mp h₁,
                (sat_char_iff_rel_aux n v hv m₂).mp h₂, rfl⟩
            · rintro ⟨m₁, m₂, h₁, h₂, rfl⟩
              exact ⟨m₁, m₂, rfl, (sat_char_iff_rel_aux n u hu m₁).mpr h₁,
                (sat_char_iff_rel_aux n v hv m₂).mpr h₂⟩
      | some s =>
          exact sat_char_atom_iff hs (fun x hx =>
            sat_char_iff_rel_aux n x (Nat.le_of_lt_succ (lt_of_lt_of_le
              (names_size_lt p x (mem_names_of_mem_args p x hx)) hp))) m

/-- **Satisfaction of a characteristic formula is bag matching.**  A bag
satisfies `char p` exactly when it matches the components of `p` atom for
atom. -/
theorem sat_char_iff_rel (p : Comb) (m : Multiset Comb) :
    Sat rhoSoup (char p) m ↔ Multiset.Rel HAtom (components p) m :=
  sat_char_iff_rel_aux (size p) p le_rfl m

/-! ## Exactness and separation -/

/-- **Characteristic formulas are exact.**  A process satisfies the
characteristic formula of `p` exactly when it is hereditarily congruent to
`p`. -/
theorem char_exact (p q : Comb) : Sat rhoSoup (char p) (components q) ↔ HCong p q :=
  (sat_char_iff_rel p (components q)).trans (hcong_iff_rel p q).symm

/-- Every process satisfies its own characteristic formula. -/
theorem char_self (p : Comb) : Sat rhoSoup (char p) (components p) :=
  (char_exact p p).mpr (.refl p)

/-- Satisfaction of a characteristic formula is invariant under hereditary
congruence of the process tested. -/
theorem sat_char_of_hcong {p q q' : Comb} (h : HCong q q')
    (hs : Sat rhoSoup (char p) (components q)) : Sat rhoSoup (char p) (components q') :=
  (char_exact p q').mpr (((char_exact p q).mp hs).trans h)

/-- **Logical separation.**  Two processes that are not hereditarily congruent
are told apart by the characteristic formula of the first. -/
theorem separates_of_not_hcong {p q : Comb} (h : ¬ HCong p q) :
    Sat rhoSoup (char p) (components p) ∧ ¬ Sat rhoSoup (char p) (components q) :=
  ⟨char_self p, fun hs => h ((char_exact p q).mp hs)⟩

/-- Characteristic formulas are a complete invariant of hereditary
congruence. -/
theorem hcong_iff_same_char (p q : Comb) :
    HCong p q ↔
      ∀ r, (Sat rhoSoup (char r) (components p) ↔ Sat rhoSoup (char r) (components q)) := by
  constructor
  · intro h r
    exact ⟨sat_char_of_hcong h, sat_char_of_hcong h.symm⟩
  · intro h
    exact (char_exact p q).mp ((h p).mp (char_self p))

/-! ## The executable checker -/

/-- Pairwise check of two argument lists under a decision on arguments. -/
def argsCheckWith (bag : Comb → Comb → Bool) : List Comb → List Comb → Bool
  | [], [] => true
  | x :: xs, y :: ys => bag x y && argsCheckWith bag xs ys
  | _, _ => false

/-- Two atoms match when they have one shape and their arguments match
pairwise as bags, with one unit of fuel less. -/
def atomCheck : Nat → Comb → Comb → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match shapeOf a, shapeOf b with
    | some s, some s' =>
        (s == s') && argsCheckWith
          (fun x y => greedy (atomCheck n) (componentList x) (componentList y))
          (args a) (args b)
    | _, _ => false

/-- **Decide hereditary congruence**: match the component bags greedily under
the atom decision. -/
def bagCheck (n : Nat) (p q : Comb) : Bool :=
  greedy (atomCheck n) (componentList p) (componentList q)

theorem argsCheckWith_iff (bag : Comb → Comb → Bool) : ∀ (xs ys : List Comb),
    (∀ x ∈ xs, ∀ y, (bag x y = true ↔ HCong x y)) →
    (argsCheckWith bag xs ys = true ↔ HCongArgs xs ys)
  | [], [], _ => by
      simp only [argsCheckWith, true_iff]; exact .nil
  | [], _ :: _, _ => by
      simp only [argsCheckWith, Bool.false_eq_true, false_iff]
      intro h; cases h
  | _ :: _, [], _ => by
      simp only [argsCheckWith, Bool.false_eq_true, false_iff]
      intro h; cases h
  | x :: xs, y :: ys, spec => by
      have hhead := spec x List.mem_cons_self y
      have htail := argsCheckWith_iff bag xs ys
        (fun z hz => spec z (List.mem_cons_of_mem x hz))
      simp only [argsCheckWith, Bool.and_eq_true]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact .cons (hhead.mp h₁) (htail.mp h₂)
      · intro h
        cases h with
        | cons h₁ h₂ => exact ⟨hhead.mpr h₁, htail.mpr h₂⟩

/-- Adequacy at one fuel level, for atoms and for bags together: each is proved
from the other one level down. -/
def Adequate (n : Nat) : Prop :=
  (∀ (a b : Comb) (s : Shape), shapeOf a = some s → size a ≤ n →
      (atomCheck n a b = true ↔ HAtom a b)) ∧
  (∀ (p q : Comb), size p ≤ n → (bagCheck n p q = true ↔ HCong p q))

theorem bagCheck_iff_of_atom {n : Nat}
    (hatom : ∀ (a b : Comb) (s : Shape), shapeOf a = some s → size a ≤ n →
      (atomCheck n a b = true ↔ HAtom a b))
    (p q : Comb) (hp : size p ≤ n) : bagCheck n p q = true ↔ HCong p q := by
  unfold bagCheck
  rw [greedy_eq_true_iff (r := HAtom) (atomCheck n) (componentList p) (componentList q)
    (fun a ha b _ =>
      let ⟨s, hs⟩ := shape_of_mem_componentList ha
      hatom a b s hs ((size_le_of_mem_componentList p a ha).trans hp)),
    hcong_iff_rel, components_eq_coe, components_eq_coe]

/-- The defining equation of `atomCheck` at known shapes.  Stated so that the
inner bag decision appears as the same term the argument lemma is about. -/
theorem atomCheck_succ_shapes {n : Nat} {a b : Comb} {s s' : Shape}
    (ha : shapeOf a = some s) (hb : shapeOf b = some s') :
    atomCheck (n + 1) a b =
      ((s == s') && argsCheckWith
        (fun x y => greedy (atomCheck n) (componentList x) (componentList y))
        (args a) (args b)) := by
  unfold atomCheck
  rw [ha, hb]

theorem atomCheck_succ_none {n : Nat} {a b : Comb} {s : Shape}
    (ha : shapeOf a = some s) (hb : shapeOf b = none) :
    atomCheck (n + 1) a b = false := by
  unfold atomCheck
  rw [ha, hb]

theorem atomCheck_succ_iff {n : Nat}
    (hbag : ∀ (p q : Comb), size p ≤ n → (bagCheck n p q = true ↔ HCong p q))
    (a b : Comb) (s : Shape) (ha : shapeOf a = some s) (hsize : size a ≤ n + 1) :
    atomCheck (n + 1) a b = true ↔ HAtom a b := by
  have hargs := argsCheckWith_iff
    (fun x y => greedy (atomCheck n) (componentList x) (componentList y))
    (args a) (args b) (fun x hx y => by
      have hlt : size x ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le
        (names_size_lt a x (mem_names_of_mem_args a x hx)) hsize)
      exact hbag x y hlt)
  cases hb : shapeOf b with
  | none =>
      rw [atomCheck_succ_none ha hb]
      simp only [Bool.false_eq_true, false_iff, HAtom, not_exists]
      intro s' hs'
      rw [hb] at hs'
      simp at hs'
  | some s' =>
      rw [atomCheck_succ_shapes ha hb, Bool.and_eq_true, beq_iff_eq, hargs]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨s, ha, hb, h⟩
      · rintro ⟨s'', ha'', hb'', h⟩
        cases Option.some.inj (ha.symm.trans ha'')
        cases Option.some.inj (hb.symm.trans hb'')
        exact ⟨rfl, h⟩

theorem adequate : ∀ n, Adequate n
  | 0 =>
      ⟨fun a _ _ _ hsize => absurd hsize (by have := size_pos a; omega),
       fun p _ hp => absurd hp (by have := size_pos p; omega)⟩
  | n + 1 =>
      have ih := adequate n
      have hatom : ∀ (a b : Comb) (s : Shape), shapeOf a = some s → size a ≤ n + 1 →
          (atomCheck (n + 1) a b = true ↔ HAtom a b) :=
        fun a b s ha hsize => atomCheck_succ_iff ih.2 a b s ha hsize
      ⟨hatom, fun p q hp => bagCheck_iff_of_atom hatom p q hp⟩

/-- **The checker agrees with hereditary congruence**, at any fuel at least the
size of the first process. -/
theorem bagCheck_iff {n : Nat} {p q : Comb} (hp : size p ≤ n) :
    bagCheck n p q = true ↔ HCong p q :=
  (adequate n).2 p q hp

/-- The checker for the characteristic fragment: does `q` satisfy `char p`? -/
def charCheck (p q : Comb) : Bool := bagCheck (size p) p q

/-- **The checker agrees with satisfaction of the characteristic formula.** -/
theorem charCheck_iff (p q : Comb) :
    charCheck p q = true ↔ Sat rhoSoup (char p) (components q) :=
  (bagCheck_iff le_rfl).trans (char_exact p q).symm

theorem charCheck_eq_false_iff (p q : Comb) :
    charCheck p q = false ↔ ¬ Sat rhoSoup (char p) (components q) := by
  rw [← charCheck_iff, Bool.not_eq_true]

/-! ## Controls

Each verdict is computed by the kernel from `charCheck` and carried to
satisfaction by `charCheck_iff`. -/

namespace CharacteristicControls

/-- Two distinct atoms. -/
def A : Comb := kk nil
def B : Comb := ev nil

-- permutation
theorem perm_check : charCheck (par A B) (par B A) = true := by decide
theorem perm : Sat rhoSoup (char (par A B)) (components (par B A)) :=
  (charCheck_iff _ _).mp perm_check

-- reassociation
theorem assoc_check : charCheck (par (par A B) A) (par A (par B A)) = true := by decide
theorem assoc : Sat rhoSoup (char (par (par A B) A)) (components (par A (par B A))) :=
  (charCheck_iff _ _).mp assoc_check

-- the parallel unit
theorem unit_check : charCheck (par A nil) A = true := by decide
theorem unit : Sat rhoSoup (char (par A nil)) (components A) :=
  (charCheck_iff _ _).mp unit_check

-- multiplicity: one component is not two, in either direction
theorem multiplicity_check : charCheck (par A A) A = false := by decide
theorem multiplicity : ¬ Sat rhoSoup (char (par A A)) (components A) :=
  (charCheck_eq_false_iff _ _).mp multiplicity_check

theorem multiplicity_converse_check : charCheck A (par A A) = false := by decide
theorem multiplicity_converse : ¬ Sat rhoSoup (char A) (components (par A A)) :=
  (charCheck_eq_false_iff _ _).mp multiplicity_converse_check

-- different constructors
theorem constructors_check : charCheck (kk nil) (ev nil) = false := by decide
theorem constructors : ¬ Sat rhoSoup (char (kk nil)) (components (ev nil)) :=
  (charCheck_eq_false_iff _ _).mp constructors_check

-- different quoted arguments
theorem arguments_check : charCheck (kk nil) (kk (kk nil)) = false := by decide
theorem arguments : ¬ Sat rhoSoup (char (kk nil)) (components (kk (kk nil))) :=
  (charCheck_eq_false_iff _ _).mp arguments_check

-- quoted arguments are compared up to congruence, hereditarily
theorem quoted_unit_check : charCheck (kk (par nil nil)) (kk nil) = true := by decide
theorem quoted_unit : Sat rhoSoup (char (kk (par nil nil))) (components (kk nil)) :=
  (charCheck_iff _ _).mp quoted_unit_check

theorem quoted_depth_two_check :
    charCheck (kk (kk (par nil nil))) (kk (kk nil)) = true := by decide

theorem quoted_perm_check :
    charCheck (fw (par A B) (kk (par B A))) (fw (par B A) (kk (par A B))) = true := by decide

/-! ### The boundary between the two congruences

The formulas characterize `HCong`.  On the quoted-unit pair the two relations
disagree: the formula accepts, `HCong` holds, and `Cong` fails.  So a
characteristic formula is *not* a characteristic formula for `Cong`. -/

theorem quoted_unit_hcong : HCong (kk (par nil nil)) (kk nil) :=
  (charCheck_iff _ _).mp quoted_unit_check |> (char_exact _ _).mp

theorem quoted_unit_not_cong : ¬ Cong (kk (par nil nil)) (kk nil) :=
  not_cong_quoted_unit

theorem char_does_not_characterize_cong :
    ∃ p q, Sat rhoSoup (char p) (components q) ∧ ¬ Cong p q :=
  ⟨kk (par nil nil), kk nil, quoted_unit, quoted_unit_not_cong⟩

theorem multiplicity_not_hcong : ¬ HCong (par A A) A :=
  fun h => absurd ((char_exact _ _).mpr h) multiplicity

end CharacteristicControls

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.char_exact
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.separates_of_not_hcong
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.hcong_iff_same_char
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.bagCheck_iff
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.charCheck_iff
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.CharacteristicControls.perm
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.CharacteristicControls.multiplicity
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.CharacteristicControls.quoted_unit
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.CharacteristicControls.char_does_not_characterize_cong
