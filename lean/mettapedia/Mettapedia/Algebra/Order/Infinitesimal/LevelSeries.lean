import Mettapedia.Algebra.Order.Infinitesimal.LevelField

/-!
# An executable representation of the level field

`LevelField` is a `HahnSeries`, which stores a coefficient *function* and is
therefore noncomputable.  This module supplies the finite data a program can
actually hold — a list of level/coefficient pairs — together with arithmetic
that runs, and proves the list denotes what the arithmetic says it does.

The design keeps two things apart that are easy to conflate.

* **Denotation** (`toHahn`) is defined on *arbitrary* lists, with no invariant:
  a list denotes the sum of its terms.  Repeated levels and zero coefficients
  are allowed and denote exactly what they should.  This is what makes the
  homomorphism theorems clean — `add` is list append, and
  `toHahn_append` is `List.sum_append`.
* **Canonical form** (`norm`) is a separate operation that merges repeated
  levels, drops zero coefficients and sorts.  `toHahn_norm` proves it changes
  no value, so canonicalisation is an optimisation and never a semantic step.

Multiplication is the pairwise product of terms, and `toHahn_mul` proves it is
the field's multiplication.  Nothing here uses the order, so nothing here has
to be re-proved when the order is brought in.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries

/-- A term: a coefficient at a level. -/
abbrev Term : Type := ℤ × ℚ

/-- The finite data a program holds. -/
abbrev LevelSeries : Type := List Term

namespace LevelSeries

/-! ## Denotation -/

/-- What a list of terms denotes: the sum of its terms. -/
noncomputable def toHahn (l : LevelSeries) : HahnSeries ℤ ℚ :=
  (l.map fun t => single t.1 t.2).sum

/-- Its image in the ordered field. -/
noncomputable def toLevelField (l : LevelSeries) : LevelField := toLex (toHahn l)

@[simp] theorem toHahn_nil : toHahn [] = 0 := rfl

@[simp] theorem toHahn_cons (t : Term) (l : LevelSeries) :
    toHahn (t :: l) = single t.1 t.2 + toHahn l := by
  simp [toHahn]

/-! ## Addition is append -/

/-- Addition: concatenate the terms. -/
def add (p q : LevelSeries) : LevelSeries := p ++ q

@[simp] theorem toHahn_append (p q : LevelSeries) :
    toHahn (p ++ q) = toHahn p + toHahn q := by
  simp [toHahn, List.map_append, List.sum_append]

/-- **Addition is the field's addition.** -/
theorem toHahn_add (p q : LevelSeries) : toHahn (add p q) = toHahn p + toHahn q :=
  toHahn_append p q

/-! ## Negation -/

/-- Negation: negate every coefficient. -/
def neg (p : LevelSeries) : LevelSeries := p.map fun t => (t.1, -t.2)

/-- **Negation is the field's negation.** -/
theorem toHahn_neg (p : LevelSeries) : toHahn (neg p) = - toHahn p := by
  induction p with
  | nil => simp [neg]
  | cons t l ih =>
      simp only [neg, List.map_cons] at *
      rw [toHahn_cons, toHahn_cons, ih, single_neg, neg_add]

/-- Subtraction. -/
def sub (p q : LevelSeries) : LevelSeries := add p (neg q)

theorem toHahn_sub (p q : LevelSeries) : toHahn (sub p q) = toHahn p - toHahn q := by
  rw [sub, toHahn_add, toHahn_neg, sub_eq_add_neg]

/-! ## Multiplication -/

/-- One term against a whole series. -/
def scaleTerm (t : Term) (q : LevelSeries) : LevelSeries :=
  q.map fun u => (t.1 + u.1, t.2 * u.2)

theorem toHahn_scaleTerm (t : Term) (q : LevelSeries) :
    toHahn (scaleTerm t q) = single t.1 t.2 * toHahn q := by
  induction q with
  | nil => simp [scaleTerm]
  | cons u l ih =>
      simp only [scaleTerm, List.map_cons] at *
      rw [toHahn_cons, toHahn_cons, ih, mul_add, single_mul_single]

/-- Multiplication: every term against every term. -/
def mul (p q : LevelSeries) : LevelSeries :=
  p.flatMap fun t => scaleTerm t q

/-- **Multiplication is the field's multiplication.** -/
theorem toHahn_mul (p q : LevelSeries) : toHahn (mul p q) = toHahn p * toHahn q := by
  induction p with
  | nil => simp [mul]
  | cons t l ih =>
      simp only [mul, List.flatMap_cons] at *
      rw [toHahn_append, toHahn_scaleTerm, ih, toHahn_cons, add_mul]

/-! ## The generators, as data -/

/-- `1`, as a one-term list. -/
def one : LevelSeries := [(0, 1)]

/-- `Ω`, as a one-term list. -/
def omega : LevelSeries := [(-1, 1)]

/-- `Ω⁻¹`, as a one-term list. -/
def omegaInv : LevelSeries := [(1, 1)]

/-- A rational, as a one-term list. -/
def ofRat (q : ℚ) : LevelSeries := [(0, q)]

@[simp] theorem toHahn_one : toHahn one = 1 := by
  simp [one, toHahn]

theorem toLevelField_omega : toLevelField omega = Om := by
  simp [toLevelField, toHahn, omega, Om]

theorem toLevelField_omegaInv : toLevelField omegaInv = omInv := by
  simp [toLevelField, toHahn, omegaInv, omInv]

/-- **The executable product of the two generators is one**, and it computes:
`mul omega omegaInv` reduces to `[(0, 1)]`. -/
theorem mul_omega_omegaInv : mul omega omegaInv = one := by
  norm_num [mul, omega, omegaInv, one, scaleTerm]

/-- And the denotation agrees with the field law proved in `LevelField`. -/
theorem toLevelField_mul_omega_omegaInv :
    toLevelField (mul omega omegaInv) = 1 := by
  rw [mul_omega_omegaInv, toLevelField, toHahn_one]
  rfl

/-! ## Canonical form

Merging repeated levels, dropping zero coefficients and sorting is an
optimisation: `toHahn_norm` proves it preserves the denotation exactly, so a
program may canonicalise whenever it likes and never at the cost of meaning. -/

/-- Insert one term into a list kept sorted by level, merging on collision and
dropping a coefficient that cancels. -/
def insertTerm (t : Term) : LevelSeries → LevelSeries
  | [] => if t.2 = 0 then [] else [t]
  | u :: rest =>
      if t.1 = u.1 then
        (if t.2 + u.2 = 0 then rest else (t.1, t.2 + u.2) :: rest)
      else if t.1 < u.1 then
        (if t.2 = 0 then u :: rest else t :: u :: rest)
      else u :: insertTerm t rest

/-- Canonical form. -/
def norm : LevelSeries → LevelSeries
  | [] => []
  | t :: rest => insertTerm t (norm rest)

theorem toHahn_insertTerm (t : Term) (l : LevelSeries) :
    toHahn (insertTerm t l) = single t.1 t.2 + toHahn l := by
  induction l with
  | nil =>
      by_cases h : t.2 = 0
      · rw [show insertTerm t [] = [] by rw [insertTerm]; simp [h]]
        rw [toHahn_nil, h, single_eq_zero, add_zero]
      · rw [show insertTerm t [] = [t] by rw [insertTerm]; simp [h]]
        simp [toHahn]
  | cons u rest ih =>
      by_cases h1 : t.1 = u.1
      · by_cases h2 : t.2 + u.2 = 0
        · rw [show insertTerm t (u :: rest) = rest by rw [insertTerm]; simp [h1, h2]]
          rw [toHahn_cons, ← add_assoc, h1, ← single_add, h2, single_eq_zero, zero_add]
        · rw [show insertTerm t (u :: rest) = (t.1, t.2 + u.2) :: rest by
                rw [insertTerm]; simp [h1, h2]]
          rw [toHahn_cons, toHahn_cons, ← add_assoc]
          congr 1
          rw [h1, single_add]
      · by_cases h3 : t.1 < u.1
        · by_cases h4 : t.2 = 0
          · rw [show insertTerm t (u :: rest) = u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]]
            rw [h4, single_eq_zero, zero_add]
          · rw [show insertTerm t (u :: rest) = t :: u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]]
            rw [toHahn_cons]
        · rw [show insertTerm t (u :: rest) = u :: insertTerm t rest by
                rw [insertTerm]; simp [h1, h3]]
          rw [toHahn_cons, ih, toHahn_cons, add_left_comm]

/-- **Canonicalisation preserves the value.** -/
theorem toHahn_norm (l : LevelSeries) : toHahn (norm l) = toHahn l := by
  induction l with
  | nil => rfl
  | cons t rest ih => rw [norm, toHahn_insertTerm, ih, toHahn_cons]

theorem toLevelField_norm (l : LevelSeries) :
    toLevelField (norm l) = toLevelField l := by
  rw [toLevelField, toLevelField, toHahn_norm]

/-! ## Canonical form is genuinely canonical

`norm` produces a list whose levels strictly increase and whose coefficients
are all nonzero.  That is what lets the sign be read straight off the head: the
head sits at the lowest level, hence the largest magnitude. -/

/-- The head's level is strictly below every later level. -/
def Sorted : LevelSeries → Prop
  | [] => True
  | t :: rest => (∀ u ∈ rest, t.1 < u.1) ∧ Sorted rest

/-- No term carries a zero coefficient. -/
def NoZero (l : LevelSeries) : Prop := ∀ t ∈ l, t.2 ≠ 0

/-- Canonical: sorted, with no vanishing term. -/
def Normalized (l : LevelSeries) : Prop := Sorted l ∧ NoZero l

/-- Inserting can introduce a term only at the inserted level. -/
theorem mem_insertTerm_level {t v : Term} : ∀ {l : LevelSeries}, v ∈ insertTerm t l →
    v.1 = t.1 ∨ v ∈ l
  | [], hv => by
      by_cases h : t.2 = 0
      · rw [show insertTerm t [] = [] by rw [insertTerm]; simp [h]] at hv; simp at hv
      · rw [show insertTerm t [] = [t] by rw [insertTerm]; simp [h]] at hv
        rcases List.mem_singleton.mp hv with rfl; exact Or.inl rfl
  | u :: rest, hv => by
      by_cases h1 : t.1 = u.1
      · by_cases h2 : t.2 + u.2 = 0
        · rw [show insertTerm t (u :: rest) = rest by rw [insertTerm]; simp [h1, h2]] at hv
          exact Or.inr (List.mem_cons_of_mem u hv)
        · rw [show insertTerm t (u :: rest) = (t.1, t.2 + u.2) :: rest by
                rw [insertTerm]; simp [h1, h2]] at hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem u hv')
      · by_cases h3 : t.1 < u.1
        · by_cases h4 : t.2 = 0
          · rw [show insertTerm t (u :: rest) = u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]] at hv
            exact Or.inr hv
          · rw [show insertTerm t (u :: rest) = t :: u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]] at hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact Or.inl rfl
            · exact Or.inr hv'
        · rw [show insertTerm t (u :: rest) = u :: insertTerm t rest by
                rw [insertTerm]; simp [h1, h3]] at hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact Or.inr List.mem_cons_self
          · rcases mem_insertTerm_level hv' with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem u h)

theorem sorted_insertTerm (t : Term) : ∀ {l : LevelSeries}, Sorted l →
    Sorted (insertTerm t l)
  | [], _ => by
      by_cases h : t.2 = 0
      · rw [show insertTerm t [] = [] by rw [insertTerm]; simp [h]]; trivial
      · rw [show insertTerm t [] = [t] by rw [insertTerm]; simp [h]]
        exact ⟨by simp, trivial⟩
  | u :: rest, hs => by
      by_cases h1 : t.1 = u.1
      · by_cases h2 : t.2 + u.2 = 0
        · rw [show insertTerm t (u :: rest) = rest by rw [insertTerm]; simp [h1, h2]]
          exact hs.2
        · rw [show insertTerm t (u :: rest) = (t.1, t.2 + u.2) :: rest by
                rw [insertTerm]; simp [h1, h2]]
          exact ⟨fun v hv => h1 ▸ hs.1 v hv, hs.2⟩
      · by_cases h3 : t.1 < u.1
        · by_cases h4 : t.2 = 0
          · rw [show insertTerm t (u :: rest) = u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]]
            exact hs
          · rw [show insertTerm t (u :: rest) = t :: u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]]
            refine ⟨?_, hs⟩
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact h3
            · exact h3.trans (hs.1 v hv')
        · rw [show insertTerm t (u :: rest) = u :: insertTerm t rest by
                rw [insertTerm]; simp [h1, h3]]
          refine ⟨?_, sorted_insertTerm t hs.2⟩
          intro v hv
          have hut : u.1 < t.1 := lt_of_le_of_ne (not_lt.mp h3) (Ne.symm h1)
          rcases mem_insertTerm_level hv with hlev | hv'
          · rw [hlev]; exact hut
          · exact hs.1 v hv'

theorem noZero_insertTerm (t : Term) : ∀ {l : LevelSeries}, NoZero l →
    NoZero (insertTerm t l)
  | [], _ => by
      by_cases h : t.2 = 0
      · rw [show insertTerm t [] = [] by rw [insertTerm]; simp [h]]; simp [NoZero]
      · rw [show insertTerm t [] = [t] by rw [insertTerm]; simp [h]]
        intro v hv; rcases List.mem_singleton.mp hv with rfl; exact h
  | u :: rest, hz => by
      by_cases h1 : t.1 = u.1
      · by_cases h2 : t.2 + u.2 = 0
        · rw [show insertTerm t (u :: rest) = rest by rw [insertTerm]; simp [h1, h2]]
          exact fun v hv => hz v (List.mem_cons_of_mem u hv)
        · rw [show insertTerm t (u :: rest) = (t.1, t.2 + u.2) :: rest by
                rw [insertTerm]; simp [h1, h2]]
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact h2
          · exact hz v (List.mem_cons_of_mem u hv')
      · by_cases h3 : t.1 < u.1
        · by_cases h4 : t.2 = 0
          · rw [show insertTerm t (u :: rest) = u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]]
            exact hz
          · rw [show insertTerm t (u :: rest) = t :: u :: rest by
                  rw [insertTerm]; simp [h1, h3, h4]]
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact h4
            · exact hz v hv'
        · rw [show insertTerm t (u :: rest) = u :: insertTerm t rest by
                rw [insertTerm]; simp [h1, h3]]
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact hz v List.mem_cons_self
          · exact noZero_insertTerm t
              (fun w hw => hz w (List.mem_cons_of_mem u hw)) v hv'

/-- **`norm` is canonical.** -/
theorem normalized_norm : ∀ l : LevelSeries, Normalized (norm l)
  | [] => ⟨trivial, by simp [NoZero, norm]⟩
  | t :: rest => by
      obtain ⟨hs, hz⟩ := normalized_norm rest
      exact ⟨sorted_insertTerm t hs, noZero_insertTerm t hz⟩

/-! ## Reading the sign off the head -/

theorem coeff_toHahn_of_all_gt {j : ℤ} : ∀ {l : LevelSeries}, (∀ u ∈ l, j < u.1) →
    (toHahn l).coeff j = 0
  | [], _ => by simp
  | u :: rest, h => by
      rw [toHahn_cons, coeff_add, coeff_single_of_ne (ne_of_lt (h u List.mem_cons_self)),
        coeff_toHahn_of_all_gt (fun v hv => h v (List.mem_cons_of_mem u hv)), add_zero]

theorem coeff_toHahn_head {i : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) : (toHahn ((i, a) :: rest)).coeff i = a := by
  rw [toHahn_cons, coeff_add, coeff_single_same,
    coeff_toHahn_of_all_gt (fun u hu => hs.1 u hu), add_zero]

theorem coeff_toHahn_lt_head {i j : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) (hj : j < i) :
    (toHahn ((i, a) :: rest)).coeff j = 0 :=
  coeff_toHahn_of_all_gt (by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact hj
    · exact hj.trans (hs.1 u hu'))

theorem toLevelField_pos_of_head {i : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) (ha : 0 < a) :
    0 < toLevelField ((i, a) :: rest) := by
  rw [toLevelField, show (0 : LevelField) = toLex (0 : HahnSeries ℤ ℚ) from rfl, lt_iff]
  refine ⟨i, fun j hj => ?_, ?_⟩
  · rw [ofLex_toLex, ofLex_toLex, coeff_toHahn_lt_head hs hj, coeff_zero]
  · rw [ofLex_toLex, ofLex_toLex, coeff_toHahn_head hs, coeff_zero]
    exact ha

theorem toLevelField_neg_of_head {i : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) (ha : a < 0) :
    toLevelField ((i, a) :: rest) < 0 := by
  rw [toLevelField, show (0 : LevelField) = toLex (0 : HahnSeries ℤ ℚ) from rfl, lt_iff]
  refine ⟨i, fun j hj => ?_, ?_⟩
  · rw [ofLex_toLex, ofLex_toLex, coeff_toHahn_lt_head hs hj, coeff_zero]
  · rw [ofLex_toLex, ofLex_toLex, coeff_toHahn_head hs, coeff_zero]
    exact ha

/-! ## Comparison

Comparison is by subtraction: canonicalise the difference and read the sign of
its head, which is its term of largest magnitude. -/

/-- The sign of a canonical series, read from its head. -/
def signOf : LevelSeries → Ordering
  | [] => .eq
  | (_, a) :: _ => if 0 < a then .gt else .lt

/-- Compare by canonicalising the difference. -/
def cmp (p q : LevelSeries) : Ordering := signOf (norm (sub p q))

/-- Executable strict order. -/
def lt (p q : LevelSeries) : Prop := cmp p q = .lt

instance (p q : LevelSeries) : Decidable (lt p q) := by
  unfold lt; infer_instance

/-- **The head's sign is the sign of the value.** -/
theorem signOf_eq_lt_iff {l : LevelSeries} (hn : Normalized l) :
    signOf l = .lt ↔ toLevelField l < 0 := by
  cases l with
  | nil =>
      rw [toLevelField, toHahn_nil]
      simp only [signOf, reduceCtorEq, false_iff, not_lt]
      exact le_of_eq rfl
  | cons t rest =>
      obtain ⟨i, a⟩ := t
      have hane : a ≠ 0 := hn.2 (i, a) List.mem_cons_self
      by_cases hpos : 0 < a
      · simp only [signOf, hpos, if_true, reduceCtorEq, false_iff, not_lt]
        exact (toLevelField_pos_of_head hn.1 hpos).le
      · have hneg : a < 0 := lt_of_le_of_ne (not_lt.mp hpos) hane
        simp only [signOf, hpos, if_false, true_iff]
        exact toLevelField_neg_of_head hn.1 hneg

/-- **The executable comparison agrees with the field order.**  Nothing about
the order was assumed of the representation: it is read off the canonical form
and matched against the order upstream already proved. -/
theorem toLevelField_sub (p q : LevelSeries) :
    toLevelField (sub p q) = toLevelField p - toLevelField q := by
  show toLex (toHahn (sub p q)) = toLex (toHahn p) - toLex (toHahn q)
  rw [toHahn_sub]
  rfl

theorem lt_iff_toLevelField_lt (p q : LevelSeries) :
    lt p q ↔ toLevelField p < toLevelField q := by
  rw [lt, cmp, signOf_eq_lt_iff (normalized_norm _), toLevelField_norm, toLevelField_sub]
  exact sub_neg

/-! ## Controls: the arithmetic runs -/

/-- `Ω + Ω = 2Ω`, computed. -/
theorem two_omega : norm (add omega omega) = [(-1, 2)] := by
  norm_num [norm, insertTerm, add, omega]

/-- `Ω − Ω = 0`, computed: the cancellation is dropped, not carried. -/
theorem omega_sub_omega : norm (sub omega omega) = [] := by
  norm_num [norm, insertTerm, sub, add, neg, omega]

/-- `(Ω + 1)(Ω − 1) = Ω² − 1`, computed. -/
theorem difference_of_squares :
    norm (mul [(-1, 1), (0, 1)] [(-1, 1), (0, -1)]) = [(-2, 1), (0, -1)] := by
  norm_num [norm, insertTerm, mul, scaleTerm]

/-- A multi-scale value: `3Ω − 5 + 2Ω⁻¹`, already canonical. -/
def sample : LevelSeries := [(-1, 3), (0, -5), (1, 2)]

theorem sample_norm : norm sample = sample := by
  norm_num [norm, insertTerm, sample]

end LevelSeries

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.LevelSeries.toHahn_add
#print axioms Mettapedia.Algebra.Order.Infinitesimal.LevelSeries.toHahn_neg
#print axioms Mettapedia.Algebra.Order.Infinitesimal.LevelSeries.toHahn_mul
#print axioms Mettapedia.Algebra.Order.Infinitesimal.LevelSeries.toHahn_norm
#print axioms Mettapedia.Algebra.Order.Infinitesimal.LevelSeries.mul_omega_omegaInv
#print axioms Mettapedia.Algebra.Order.Infinitesimal.LevelSeries.difference_of_squares
