import Mettapedia.GSLT.LanguageDef.Collections.TypedCertificates
import Mettapedia.GSLT.LanguageDef.Collections.StructureByProof

/-!
# Typed folds are faster than untyped ones

A recognized structural recursion answers on any term as on the end of its
maximal spine, folded over the cells (`StructureByProof.Recognized.answers_spine`).
Untyped, a native fold must test every cell's shape and every element's class,
and call the interpreter on the end, which may be anything. A recorded
judgment `(List Number)` or `Nat` discharges all three: the spine ends in `Nil`
or `Z`, the elements are grounded integers, and a numeral is its count
(`TypedCertificates.typed_list_spine`, `number_inversion`, `typed_nat_numeral`).

* **Exact answers.** On a term judged `(List Number)`, a recognized recursion's
  answers are its answers at `Nil`, folded over the term's integers
  (`certified_list_answers`); on a term judged `Nat`, its answers at `Z`, folded
  over the count's units (`certified_nat_answers`), and for an affine step the
  fold of a count is its summary (`certified_nat_affine`): `toint` is the count.
* **Cheaper.** In the cost model of a pass, the untyped fold pays a walk, a
  shape test, a class test and a step per cell and an end call
  (`untypedPass`); the certified fold pays one lookup of the recorded judgment,
  as `TypedCertificates.Judgment.cost_hit` says, a walk and a step per cell and
  the base's known answers (`certifiedPass`). It is cheaper on every list as
  soon as the lookup and the base cost no more than the end call, and every
  cell's tests cost something (`certifiedPass_lt_untypedPass`); its cost per
  cell is the walk and the step alone (`certifiedPass_per_cell`). A certified
  natural with a count layout folds an affine step in one step whatever its
  count (`countPass`, `countPass_lt_untypedPass`).
* **The measured case.** With 370 instructions per element for the untyped
  pass and 45 for the certified one, the certified pass of `n ≥ 1` elements
  is cheaper whenever the end call costs at least the lookup and the base
  (`Controls.measured_pass`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFolds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open TypedCertificates
open StructureByProof
open Presentations (Family binary unary numeral)

/-! ## Exact answers -/

/-- **A certified fold over a typed list answers as the recursion**: on a term
judged `(List Number)`, the answers are those at `Nil`, each folded over the
term's elements, which are grounded integers. -/
theorem certified_list_answers {β ε : Type} {answers : Atom → Multiset (β × ε)}
    (R : Recognized (binary "Cons") answers) (t : Atom) (judged : ([], Base.list) ∈ judge t) :
    answers t = (answers (.symbol "Nil")).map (R.foldFields ((binary "Cons").spine t).elems) ∧
      ∀ x ∈ ((binary "Cons").spine t).elems, ∃ n, x = .grounded (.int n) := by
  obtain ⟨stop, ints⟩ := typed_list_spine t judged
  refine ⟨?_, ints⟩
  rw [R.answers_spine t]
  congr 2
  rw [stop]

/-- **A certified fold over a typed natural answers as the recursion**: a term
judged `Nat` is the numeral of a count, and its answers are those at `Z`, each
folded over the count's units. -/
theorem certified_nat_answers {β ε : Type} {answers : Atom → Multiset (β × ε)}
    (R : Recognized (unary "S") answers) (t : Atom) (judged : ([], Base.nat) ∈ judge t) :
    ∃ k, t = numeral "S" (.symbol "Z") k ∧
      answers t = (answers (.symbol "Z")).map (R.foldFields (List.replicate k ())) := by
  obtain ⟨k, rfl⟩ := typed_nat_numeral t judged
  exact ⟨k, rfl, R.answers_build _ _⟩

/-- For an affine step, the fold of `k` units is the summary of `k` units: the
count determines it. -/
theorem certified_nat_affine {R : Type} [CommRing R] (e : R) (B : R) (k : ℕ) (z : R) :
    (List.replicate k ()).foldr (fun _ b => e + B * b) z = (summary (fun _ => e) B (List.replicate k ())).apply z :=
  foldr_eq_summary (fun _ => e) B _ z

/-- The count of a natural is its value for `toint`: one more per unit. -/
theorem toint_count (k : ℕ) :
    (List.replicate k ()).foldr (fun _ b => (1 : ℤ) + 1 * b) 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.foldr_cons, ih]
      push_cast
      ring

/-! ## The cost of a pass -/

/-- The costs of one fold pass: per cell, the walk to the next cell, the shape
test of the cell, the class test of its element and the step; at the end, a
call of the interpreter on the spine's end, or the known answers of the base;
and the lookup of a recorded judgment. -/
structure PassCosts where
  walk : ℕ
  shape : ℕ
  classTest : ℕ
  step : ℕ
  endCall : ℕ
  base : ℕ
  lookup : ℕ

/-- The untyped recognized fold over `n` cells. -/
def untypedPass (c : PassCosts) (n : ℕ) : ℕ := n * (c.walk + c.shape + c.classTest + c.step) + c.endCall

/-- The certified fold over `n` cells: the recorded judgment read once, a walk and
a step per cell, and the base. -/
def certifiedPass (c : PassCosts) (n : ℕ) : ℕ := c.lookup + n * (c.walk + c.step) + c.base

/-- **The certified fold is cheaper on every list** once the lookup and the base
cost no more than the end call and the tests of a cell cost something. -/
theorem certifiedPass_lt_untypedPass (c : PassCosts) (n : ℕ) (ends : c.lookup + c.base ≤ c.endCall)
    (tests : 0 < c.shape + c.classTest) (cells : 1 ≤ n) : certifiedPass c n < untypedPass c n := by
  unfold certifiedPass untypedPass
  have : n * (c.walk + c.shape + c.classTest + c.step) =
      n * (c.walk + c.step) + n * (c.shape + c.classTest) := by ring
  have pos : 0 < n * (c.shape + c.classTest) := Nat.mul_pos cells tests
  omega

/-- Without cells the certified fold costs no more than the untyped one. -/
theorem certifiedPass_le_untypedPass (c : PassCosts) (n : ℕ) (ends : c.lookup + c.base ≤ c.endCall) :
    certifiedPass c n ≤ untypedPass c n := by
  unfold certifiedPass untypedPass
  have : n * (c.walk + c.shape + c.classTest + c.step) =
      n * (c.walk + c.step) + n * (c.shape + c.classTest) := by ring
  omega

/-- **Per cell, the certified fold pays the walk and the step alone.** -/
theorem certifiedPass_per_cell (c : PassCosts) (n : ℕ) :
    certifiedPass c (n + 1) = certifiedPass c n + (c.walk + c.step) ∧
      untypedPass c (n + 1) = untypedPass c n + (c.walk + c.shape + c.classTest + c.step) := by
  constructor <;> simp only [certifiedPass, untypedPass] <;> ring

/-- A certified natural with a count layout: an affine step folds in one step,
whatever the count. -/
def countPass (c : PassCosts) (_k : ℕ) : ℕ := c.lookup + c.step + c.base

/-- **A count-layout natural folds in constant time**, below the untyped fold
over its cells once it has one. -/
theorem countPass_lt_untypedPass (c : PassCosts) (k : ℕ) (ends : c.lookup + c.base ≤ c.endCall)
    (walks : 0 < c.walk + c.shape + c.classTest) (cells : 1 ≤ k) : countPass c k < untypedPass c k := by
  unfold countPass untypedPass
  have : k * (c.walk + c.shape + c.classTest + c.step) ≥ c.walk + c.shape + c.classTest + c.step := by
    calc k * (c.walk + c.shape + c.classTest + c.step)
        ≥ 1 * (c.walk + c.shape + c.classTest + c.step) := Nat.mul_le_mul_right _ cells
      _ = c.walk + c.shape + c.classTest + c.step := one_mul _
  omega

/-- The recorded judgment costs one lookup, what a value class costs, and the
full judgment of the `k`-th accumulator of the build loop costs `3k + 4`
visits: the certificate the fold reads is cheap to keep. -/
theorem certificate_cost {Sig : Type} {J : Type} (Rj : Judgment Sig J) (σ : Sig) (k : ℕ) :
    Judgment.cost (memoUpTo Rj σ k) (acc (k + 1)) = 4 ∧
      Judgment.cost (fun _ => (none : Option J)) (acc (k + 1)) = 3 * k + 4 :=
  ⟨cost_step Rj σ k, cost_full_step k⟩

/-! ## Controls -/

namespace Controls

/-- **The measured pass**: 370 instructions per element untyped and 45 certified
(the per-cell costs of the inventory and the target of the goal); with an end
call that costs at least the lookup and the base, every nonempty list is
cheaper certified. -/
theorem measured_pass (endCall lookup base : ℕ) (ends : lookup + base ≤ endCall) (n : ℕ)
    (cells : 1 ≤ n) :
    certifiedPass ⟨40, 300, 25, 5, endCall, base, lookup⟩ n <
      untypedPass ⟨40, 300, 25, 5, endCall, base, lookup⟩ n :=
  certifiedPass_lt_untypedPass _ n ends (by norm_num) cells

/-- The two passes per cell: 45 and 370 instructions. -/
theorem measured_per_cell (endCall lookup base : ℕ) :
    (40 + 5 = 45) ∧ (40 + 300 + 25 + 5 = 370) ∧
      certifiedPass ⟨40, 300, 25, 5, endCall, base, lookup⟩ 1 =
        certifiedPass ⟨40, 300, 25, 5, endCall, base, lookup⟩ 0 + 45 := by
  refine ⟨rfl, rfl, ?_⟩
  have := (certifiedPass_per_cell ⟨40, 300, 25, 5, endCall, base, lookup⟩ 0).1
  simpa using this

/-- **The certificate is needed**: an untyped `(Cons 1 foo)` ends in `foo`, not
`Nil`, so a fold that skipped the end call would lose its answers there; it has
no list judgment, and no certified fold applies. -/
theorem uncertified_end :
    ((binary "Cons").spine (cell (.grounded (.int 1)) (.symbol "foo"))).stop = .symbol "foo" ∧
      ([], Base.list) ∉ judge (cell (.grounded (.int 1)) (.symbol "foo")) := by
  refine ⟨?_, TypedCertificates.Controls.improper_has_no_judgment.2⟩
  rw [TypedCertificates.Controls.improper_has_no_judgment.1]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFolds
