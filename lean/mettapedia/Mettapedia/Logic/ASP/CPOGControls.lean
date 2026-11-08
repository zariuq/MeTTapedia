import Mettapedia.Logic.ASP.CPOG
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Controls for the CPOG checker

Values are computed by the kernel (`decide`, and `decide +kernel` for the counts
in `ℚ`); the `#eval` lines run the compiled checker on the same certificates. Data variables are numbered from 1, input
clauses are numbered from 1 in input order, and extension variables follow the
data variables.

## Accepted certificates

* `x₁ ∨ x₂` as `x₁ + ¬x₁ · x₂`: one product, one sum whose exclusion is proved
  from a defining clause, the root's unit clause added by RUP from the input and
  the definitions, the input clause deleted by RUP from the definitions and the
  root. Three models.
* `(x₁ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂)` as `x₁ · ¬x₂ + ¬x₁ · x₂`: the root's unit clause
  needs an intermediate RUP lemma, which is deleted again (by RUP) before the
  end. Two models.
* `(x₁ ∨ x₂) ∧ x₃` as a product of the first POG with `x₃`: a product whose
  argument is a node. Three models over three variables.
* `¬x₁ ∨ ¬x₂` as the negation of the product `x₁ · x₂`: a negated edge, read as
  the deterministic sum `¬x₁ + x₁ · (¬x₂ + x₂ · ⊥)`. Three models.
* The unsatisfiable `x₁ ∧ ¬x₁` as the negation of the empty product: the root is
  the constant false, and the count is 0.

For each, the certified circuit is computed, `pog_sound` gives its properties,
and the certified count (`certifiedCount`, on the graph) is the model count
computed from the input.

## Rejected mutants

* A sum without its exclusion proof.
* A sum whose exclusion is proved from an input clause: the reverse unit
  propagation succeeds, but exclusion must follow from the definitions alone
  (otherwise it would hold only on the models of the input).
* A product over overlapping variables, through a node.
* An addition with a hint missing.
* A wrong root.
* The deletion of a defining clause, although it is RUP from the root's unit
  clause: the definitions must stay, or the extension variables would no longer
  be determined.
* The deletion of an input clause without justification.
* A negated sum as the root, in a certificate whose other steps all pass: a
  negated sum has no decomposable reading, so it is refused by design.
* An input clause over a variable outside the data variables.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CPOGControls

open CNF CPOG Circuit

/-- A positive literal. -/
abbrev pos (x : ℕ) : Literal ℕ := ⟨x, true⟩

/-- A negative literal. -/
abbrev neg (x : ℕ) : Literal ℕ := ⟨x, false⟩

/-! ## `x₁ ∨ x₂` -/

/-- `x₁ ∨ x₂`, clause 1. -/
def orInput : Input ℕ := ⟨{1, 2}, [[pos 1, pos 2]]⟩

/-- `x₃ = ¬x₁ · x₂` (clauses 2–4), `x₄ = x₁ + x₃` (clauses 5–7), root `x₄`, its unit clause (8),
and the deletion of the input clause. -/
def orCert : Certificate ℕ :=
  [.prod 2 3 [neg 1, pos 2],
   .sum 5 4 (pos 1) (pos 3) [3],
   .root (pos 4),
   .add 8 [pos 4] [6, 7, 2, 1],
   .delete 1 [8, 5, 4]]

/-- The certified circuit: `x₁ + ¬x₁ · (x₂ · ⊤)`. -/
def orCircuit : Circuit ℕ := sum (lit 1 true) (prod (lit 1 false) (prod (lit 2 true) top))

theorem or_accepted : check orInput orCert = true := by decide

theorem or_pog : pog orInput orCert = some orCircuit := by decide

theorem or_sound : orCircuit.Decomposable ∧ orCircuit.Deterministic ∧ orCircuit.vars ⊆ orInput.vars ∧
    ∀ σ, orInput.cnf.eval σ = orCircuit.eval σ :=
  pog_sound or_pog

theorem or_count : orInput.cnf.count orInput.vars = 3 := by decide

theorem or_certified : certifiedCount ℚ orInput orCert = some 3 := by decide +kernel

/-- The certified count is the count, by the soundness theorem alone. -/
theorem or_count_certified : (3 : ℚ) = orInput.cnf.count orInput.vars :=
  certifiedCount_sound or_certified

/-! ## `(x₁ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂)` -/

/-- Exclusive or, clauses 1 and 2. -/
def xorInput : Input ℕ := ⟨{1, 2}, [[pos 1, pos 2], [neg 1, neg 2]]⟩

/-- `x₃ = x₁ · ¬x₂` (3–5), `x₄ = ¬x₁ · x₂` (6–8), `x₅ = x₃ + x₄` (9–11), the lemma `x₅ ∨ ¬x₁`
(12), the root's unit clause (13), then the deletions. -/
def xorCert : Certificate ℕ :=
  [.prod 3 3 [pos 1, neg 2],
   .prod 6 4 [neg 1, pos 2],
   .sum 9 5 (pos 3) (pos 4) [4, 7],
   .root (pos 5),
   .add 12 [pos 5, neg 1] [10, 3, 2],
   .add 13 [pos 5] [12, 11, 6, 1],
   .delete 12 [13],
   .delete 1 [13, 4, 8, 9],
   .delete 2 [13, 5, 7, 9]]

theorem xor_accepted : check xorInput xorCert = true := by decide

theorem xor_pog :
    pog xorInput xorCert = some (sum (prod (lit 1 true) (prod (lit 2 false) top))
      (prod (lit 1 false) (prod (lit 2 true) top))) := by
  decide

theorem xor_count : xorInput.cnf.count xorInput.vars = 2 := by decide

theorem xor_certified : certifiedCount ℚ xorInput xorCert = some 2 := by decide +kernel

/-! ## `(x₁ ∨ x₂) ∧ x₃` -/

/-- Clauses 1 and 2. -/
def andInput : Input ℕ := ⟨{1, 2, 3}, [[pos 1, pos 2], [pos 3]]⟩

/-- The POG of `x₁ ∨ x₂` (`x₄`, `x₅`, clauses 3–8), then `x₆ = x₅ · x₃` (9–11). -/
def andCert : Certificate ℕ :=
  [.prod 3 4 [neg 1, pos 2],
   .sum 6 5 (pos 1) (pos 4) [4],
   .prod 9 6 [pos 5, pos 3],
   .root (pos 6),
   .add 12 [pos 6] [2, 9, 7, 8, 3, 1],
   .delete 1 [12, 10, 6, 5],
   .delete 2 [12, 11]]

theorem and_accepted : check andInput andCert = true := by decide

theorem and_count : andInput.cnf.count andInput.vars = 3 := by decide

theorem and_certified : certifiedCount ℚ andInput andCert = some 3 := by decide +kernel

/-! ## `¬x₁ ∨ ¬x₂`: a negated product -/

/-- Clause 1. -/
def nandInput : Input ℕ := ⟨{1, 2}, [[neg 1, neg 2]]⟩

/-- `x₃ = x₁ · x₂` (2–4), root `¬x₃`, its unit clause (5), the deletion. -/
def nandCert : Certificate ℕ :=
  [.prod 2 3 [pos 1, pos 2],
   .root (neg 3),
   .add 5 [neg 3] [3, 4, 1],
   .delete 1 [2, 5]]

theorem nand_pog :
    pog nandInput nandCert =
      some (sum (lit 1 false) (prod (lit 1 true) (sum (lit 2 false) (prod (lit 2 true) bot)))) := by
  decide

theorem nand_count : nandInput.cnf.count nandInput.vars = 3 := by decide

theorem nand_certified : certifiedCount ℚ nandInput nandCert = some 3 := by decide +kernel

/-! ## `x₁ ∧ ¬x₁`: unsatisfiable -/

/-- Clauses 1 and 2. -/
def unsatInput : Input ℕ := ⟨{1}, [[pos 1], [neg 1]]⟩

/-- `x₂` the empty product (clause 3), root `¬x₂`, its unit clause (4), the deletions. -/
def unsatCert : Certificate ℕ :=
  [.prod 3 2 [],
   .root (neg 2),
   .add 4 [neg 2] [1, 2],
   .delete 1 [3, 4],
   .delete 2 [3, 4]]

theorem unsat_pog : pog unsatInput unsatCert = some bot := by decide

theorem unsat_count : unsatInput.cnf.count unsatInput.vars = 0 := by decide

theorem unsat_certified : certifiedCount ℚ unsatInput unsatCert = some 0 := by decide +kernel

/-! ## Rejected mutants -/

/-- A sum without its exclusion proof. -/
theorem sum_without_exclusion :
    check orInput [.prod 2 3 [neg 1, pos 2], .sum 5 4 (pos 1) (pos 3) [], .root (pos 4),
      .add 8 [pos 4] [6, 7, 2, 1], .delete 1 [8, 5, 4]] = false := by
  decide

/-- The exclusion `¬x₁ ∨ ¬x₂` is a RUP consequence of the input clause 2 of exclusive or ... -/
theorem input_exclusion_is_rup : rup [neg 1, neg 2] [[neg 1, neg 2]] = true := by decide

/-- ... but a sum's exclusion must follow from defining clauses, so the sum `x₁ + x₂` is refused. -/
theorem sum_by_input_clause : step xorInput.vars (init xorInput) (.sum 3 3 (pos 1) (pos 2) [2]) = none := by
  decide

/-- The refusal is the hint's origin: clause 2 is found, and refused as a sum hint because it is an
input clause. -/
theorem input_hint_refused :
    hintClauses (init xorInput).store (fun _ => true) [2] = some [[neg 1, neg 2]] ∧
      hintClauses (init xorInput).store (fun e => decide (e.kind = .defining)) [2] = none := by
  decide

/-- A product over overlapping variables: `x₅ = x₁ + ¬x₁ · x₂` depends on `x₁`. -/
theorem overlapping_product :
    check andInput [.prod 3 4 [neg 1, pos 2], .sum 6 5 (pos 1) (pos 4) [4], .prod 9 6 [pos 5, pos 1],
      .root (pos 6)] = false := by
  decide

/-- The same product step, refused on its own. -/
theorem overlapping_product_step :
    ((run andInput.vars (init andInput) [.prod 3 4 [neg 1, pos 2], .sum 6 5 (pos 1) (pos 4) [4]]).bind fun st =>
      step andInput.vars st (.prod 9 6 [pos 5, pos 1])) = none := by
  decide

/-- An addition with a hint missing. -/
theorem bad_rup_hint :
    check orInput [.prod 2 3 [neg 1, pos 2], .sum 5 4 (pos 1) (pos 3) [3], .root (pos 4),
      .add 8 [pos 4] [6, 7, 1], .delete 1 [8, 5, 4]] = false := by
  decide

/-- A wrong root: the product `x₃` instead of the sum `x₄`. Every step passes; the final check
fails, since the unit clause left is that of `x₄`. -/
theorem wrong_root :
    check orInput [.prod 2 3 [neg 1, pos 2], .sum 5 4 (pos 1) (pos 3) [3], .root (pos 3),
      .add 8 [pos 4] [6, 7, 2, 1], .delete 1 [8, 5, 4]] = false ∧
    (run orInput.vars (init orInput) [.prod 2 3 [neg 1, pos 2], .sum 5 4 (pos 1) (pos 3) [3], .root (pos 3),
      .add 8 [pos 4] [6, 7, 2, 1], .delete 1 [8, 5, 4]]).isSome = true := by
  decide

/-- The deletion of a defining clause is refused, even when the clause is RUP from the others: the
defining clause 6, `x₄ ∨ ¬x₁`, follows from the root's unit clause 8. -/
theorem delete_defining :
    check orInput (orCert ++ [.delete 6 [8]]) = false ∧ rup [pos 4, neg 1] [[pos 4]] = true := by
  decide

/-- The deletion of an input clause without justification. -/
theorem delete_unjustified :
    check orInput [.prod 2 3 [neg 1, pos 2], .sum 5 4 (pos 1) (pos 3) [3], .root (pos 4),
      .add 8 [pos 4] [6, 7, 2, 1], .delete 1 []] = false := by
  decide

/-- `¬x₁ ∧ ¬x₂`, clauses 1 and 2. -/
def norInput : Input ℕ := ⟨{1, 2}, [[neg 1], [neg 2]]⟩

/-- The POG of `x₁ ∨ x₂` (`x₃`, `x₄`, clauses 3–8) with root `¬x₄`. -/
def norSteps : Certificate ℕ :=
  [.prod 3 3 [neg 1, pos 2],
   .sum 6 4 (pos 1) (pos 3) [4],
   .add 9 [neg 4] [1, 2, 5, 6],
   .delete 1 [7, 9],
   .delete 2 [9, 7, 8, 3]]

/-- **A negated sum is refused**: every other step passes, and the root `¬x₄` is not admissible. -/
theorem negated_sum_root :
    check norInput (norSteps.take 2 ++ [.root (neg 4)] ++ norSteps.drop 2) = false ∧
    (run norInput.vars (init norInput) norSteps).isSome = true ∧
    ((run norInput.vars (init norInput) (norSteps.take 2)).bind fun st =>
      step norInput.vars st (.root (neg 4))) = none := by
  decide

/-- An input clause over `x₃`, outside the data variables `{x₁, x₂}`. -/
theorem input_outside_vars : check ⟨{1, 2}, [[pos 1, pos 2], [pos 3]]⟩ orCert = false := by decide

/-! ## The compiled checker -/

#eval (check orInput orCert, check xorInput xorCert, check andInput andCert, check nandInput nandCert,
  check unsatInput unsatCert)
#eval (certifiedCount ℚ orInput orCert, certifiedCount ℚ xorInput xorCert, certifiedCount ℚ andInput andCert,
  certifiedCount ℚ nandInput nandCert, certifiedCount ℚ unsatInput unsatCert)
#eval pog xorInput xorCert

end Mettapedia.Logic.ASP.CPOGControls
