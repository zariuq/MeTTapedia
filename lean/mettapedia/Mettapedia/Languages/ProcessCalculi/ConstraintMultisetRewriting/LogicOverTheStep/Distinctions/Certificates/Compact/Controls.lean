import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family

/-!
# Controls: what the lumping check must check

The lumping check compares the fibre masses of **every** state's successor distribution with the
quotient's row. Two weaker checks are natural and wrong; each accepts a certificate whose bound is
false.

* **Average lumping** (`averageCheck`): the class's states agree with the quotient on average (the sum
  of their fibre masses is the class size times the quotient's mass). On `splitChain` (two states of one
  class, one moving surely to a state reading `0`, the other surely to one reading `1`) it accepts a
  certificate claiming distance `0` between them (`average_accepts`); the test "observe next" gives
  `9/10` (`average_unsound`). The checker refuses it (`split_refused`).
* **Support lumping** (`supportCheck`): the fibre masses are positive exactly where the quotient's are.
  On `thirdsChain` (the two states move to the same two states with probabilities `1/3, 2/3` and
  `2/3, 1/3`) it accepts the same claim (`support_accepts`); the test gives `3/10`
  (`support_unsound`). The checker refuses it (`thirds_refused`).

**Brittleness.** In `perturbed`, one leaky copy of the blown-up chain at `m = 1` leaks with
probability `1/3` instead of `1/2`. The four classes are no longer a lumping (`perturbed_refused`),
and the two leaky copies are apart (`perturbed_apart`, by a test): no exact lumping merges them, so on
those copies the certificate on classes gains nothing. A quotient with error is the next form, not
this one.

**A refused claim on the family.** The class map with the leak chain's too-small kernel is refused at
every size (`tooSmallCert_refused`), and its claim is false at every size (`tooSmallCert_false`).

**The identity view.** On the leak chain itself the certificate on classes with the identity map is
accepted (`identity_accepted`) and costs the incumbent's work plus the lumping check
(`identity_work`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Controls

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family

/-! ## Two weaker checks -/

section Naive

variable {A Atom S C : Type*} [Fintype S] [Fintype C] [DecidableEq C] [Fintype A] [Fintype Atom]

/-- **Average lumping**: on every class, the fibre masses of its states sum to the class size times the
quotient's mass; observations as in the lumping check. -/
def averageCheck (P : LabelledMarkovChain ℚ A Atom S) (Q : LabelledMarkovChain ℚ A Atom C)
    (view : S → C) : Bool :=
  decide (∀ a k l, ∑ s ∈ Finset.univ.filter (fun s => view s = k), fibreMass view (P.trans a s) l =
      (Finset.univ.filter (fun s => view s = k)).card * Q.trans a k l) &&
    decide (∀ i s, P.observe i s = Q.observe i (view s))

/-- **Support lumping**: the fibre masses are positive exactly where the quotient's are; observations
as in the lumping check. -/
def supportCheck (P : LabelledMarkovChain ℚ A Atom S) (Q : LabelledMarkovChain ℚ A Atom C)
    (view : S → C) : Bool :=
  decide (∀ a s k, (fibreMass view (P.trans a s) k ≠ 0 ↔ Q.trans a (view s) k ≠ 0)) &&
    decide (∀ i s, P.observe i s = Q.observe i (view s))

end Naive

/-! ## Two states of one class with different futures -/

/-- The quotient: the class `0` moves to `1` or `2` with probability `1/2` each; `1` and `2` stay. -/
def pairTrans : Fin 3 → Fin 3 → ℚ := ![![0, 1 / 2, 1 / 2], ![0, 1, 0], ![0, 0, 1]]

theorem pairTrans_nonneg : ∀ s x, 0 ≤ pairTrans s x := by decide +kernel

theorem pairTrans_total : ∀ s, ∑ x, pairTrans s x = 1 := by decide +kernel

/-- **The quotient chain**: `2` reads `1`, the others `0`. -/
def pairQuotient : LabelledMarkovChain ℚ Unit Unit (Fin 3) where
  trans _ := pairTrans
  isDistribution _ s := ⟨pairTrans_nonneg s, pairTrans_total s⟩
  observe _ := ![0, 0, 1]

/-- The class map: `0` and `1` to the class `0`, then `2 ↦ 1`, `3 ↦ 2`. -/
def pairView : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- The quotient's prefixpoint: `9/20` between the class and `1`, one against `2`; every pair is
filled in. -/
def pairCert : Prefixpoint Unit (Fin 3) :=
  ⟨![![0, 9 / 20, 1], ![9 / 20, 0, 1], ![1, 1, 0]], fun _ _ _ => none⟩

theorem pairCert_accepted : check pairQuotient discount pairCert = true := by decide +kernel

/-- `0` moves surely to `2`, `1` surely to `3`; `2` and `3` stay. -/
def splitTrans : Fin 4 → Fin 4 → ℚ := ![![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 0, 1]]

theorem splitTrans_nonneg : ∀ s x, 0 ≤ splitTrans s x := by decide +kernel

theorem splitTrans_total : ∀ s, ∑ x, splitTrans s x = 1 := by decide +kernel

/-- **Two states of one class with opposite futures**: `3` reads `1`, the others `0`. -/
def splitChain : LabelledMarkovChain ℚ Unit Unit (Fin 4) where
  trans _ := splitTrans
  isDistribution _ s := ⟨splitTrans_nonneg s, splitTrans_total s⟩
  observe _ := ![0, 0, 0, 1]

/-- The certificate on classes claiming distance `0` between `0` and `1`. -/
def splitCert : OnClasses Unit Unit (Fin 4) (Fin 3) := ⟨pairView, pairQuotient, pairCert⟩

theorem average_accepts :
    (averageCheck splitChain pairQuotient pairView && check pairQuotient discount pairCert) = true := by
  decide +kernel

theorem split_refused : classCheck splitChain discount splitCert = false := by decide +kernel

/-- "Observe next". -/
def observeNext : List (TestNode Unit Unit) := [.observe (), .next () 0]

theorem split_gap : testGap splitChain discount observeNext 0 1 = some (9 / 10, 1) := by decide +kernel

/-- **Average lumping is unsound**: it accepts the certificate, whose bound `0` between `0` and `1`
is false: the distance is at least `9/10`. -/
theorem average_unsound :
    (averageCheck splitChain pairQuotient pairView && check pairQuotient discount pairCert) = true ∧
      (splitCert.cert.kernel (splitCert.view 0) (splitCert.view 1) : ℝ) <
        bisimulationMetric (realChain splitChain) (realChain splitChain) (discount : ℝ) 0 1 := by
  refine ⟨average_accepts, ?_⟩
  have below := testGap_le_bisimulationMetric split_gap discount_nonneg discount_lt_one.le
  have zero : splitCert.cert.kernel (splitCert.view 0) (splitCert.view 1) = 0 := by decide +kernel
  rw [zero, Rat.cast_zero]
  have nine : ((9 / 10 : ℚ) : ℝ) = 9 / 10 := by norm_num
  rw [nine] at below
  linarith

/-- `0` moves to `2, 3` with `1/3, 2/3`, `1` with `2/3, 1/3`; `2` and `3` stay. -/
def thirdsTrans : Fin 4 → Fin 4 → ℚ :=
  ![![0, 0, 1 / 3, 2 / 3], ![0, 0, 2 / 3, 1 / 3], ![0, 0, 1, 0], ![0, 0, 0, 1]]

theorem thirdsTrans_nonneg : ∀ s x, 0 ≤ thirdsTrans s x := by decide +kernel

theorem thirdsTrans_total : ∀ s, ∑ x, thirdsTrans s x = 1 := by decide +kernel

/-- **Two states of one class with the same supports and different probabilities.** -/
def thirdsChain : LabelledMarkovChain ℚ Unit Unit (Fin 4) where
  trans _ := thirdsTrans
  isDistribution _ s := ⟨thirdsTrans_nonneg s, thirdsTrans_total s⟩
  observe _ := ![0, 0, 0, 1]

def thirdsCert : OnClasses Unit Unit (Fin 4) (Fin 3) := ⟨pairView, pairQuotient, pairCert⟩

theorem support_accepts :
    (supportCheck thirdsChain pairQuotient pairView && check pairQuotient discount pairCert) = true := by
  decide +kernel

theorem thirds_refused : classCheck thirdsChain discount thirdsCert = false := by decide +kernel

theorem thirds_gap : testGap thirdsChain discount observeNext 0 1 = some (3 / 10, 1) := by decide +kernel

/-- **Support lumping is unsound**: it accepts the certificate, whose bound `0` between `0` and `1` is
false: the distance is at least `3/10`. -/
theorem support_unsound :
    (supportCheck thirdsChain pairQuotient pairView && check pairQuotient discount pairCert) = true ∧
      (thirdsCert.cert.kernel (thirdsCert.view 0) (thirdsCert.view 1) : ℝ) <
        bisimulationMetric (realChain thirdsChain) (realChain thirdsChain) (discount : ℝ) 0 1 := by
  refine ⟨support_accepts, ?_⟩
  have below := testGap_le_bisimulationMetric thirds_gap discount_nonneg discount_lt_one.le
  have zero : thirdsCert.cert.kernel (thirdsCert.view 0) (thirdsCert.view 1) = 0 := by decide +kernel
  rw [zero, Rat.cast_zero]
  have three : ((3 / 10 : ℚ) : ℝ) = 3 / 10 := by norm_num
  rw [three] at below
  linarith

/-! ## Brittleness: a perturbed copy -/

/-- The blown-up chain at `m = 1` with the copy `(2, 1)` of leaky leaking with probability `1/3`. -/
def perturbedTrans (s x : St 1) : ℚ :=
  if s = (2, 1) then 2 / 3 * dirac ((2, 0) : St 1) x + 1 / 3 * dirac ((3, 1) : St 1) x
  else blowTrans 1 s x

theorem perturbedTrans_nonneg : ∀ s x, 0 ≤ perturbedTrans s x := by decide +kernel

theorem perturbedTrans_total : ∀ s, ∑ x, perturbedTrans s x = 1 := by decide +kernel

/-- **A perturbed blow-up.** -/
def perturbed : LabelledMarkovChain ℚ Unit Unit (St 1) where
  trans _ := perturbedTrans
  isDistribution _ s := ⟨perturbedTrans_nonneg s, perturbedTrans_total s⟩
  observe _ s := ![0, 0, 0, 1] s.1

/-- **The four classes no longer lump.** -/
theorem perturbed_refused : lumpCheck perturbed leak Prod.fst = false := by decide +kernel

/-- "The sink next". -/
def sinkNext : List (TestNode Unit Unit) := [.observe (), .next () 0]

theorem perturbed_gap : testGap perturbed discount sinkNext (2, 0) (2, 1) = some (3 / 20, 1) := by
  decide +kernel

/-- **The two leaky copies are apart**: no exact lumping merges them. -/
theorem perturbed_apart :
    (3 / 20 : ℝ) ≤ bisimulationMetric (realChain perturbed) (realChain perturbed) (discount : ℝ)
      (2, 0) (2, 1) := by
  have below := testGap_le_bisimulationMetric perturbed_gap discount_nonneg discount_lt_one.le
  have value : ((3 / 20 : ℚ) : ℝ) = 3 / 20 := by norm_num
  rw [value] at below
  exact below

/-! ## A refused claim on the family, at every size -/

/-- The class map with the leak chain's too-small kernel. -/
def tooSmallCert (m : ℕ) : OnClasses Unit Unit (St m) (Fin 4) := ⟨Prod.fst, leak, tooSmall⟩

theorem tooSmallCert_refused (m : ℕ) :
    classCheck (blowup m) discount (tooSmallCert m) = false := by
  simp only [classCheck, tooSmallCert, tooSmall_refused, Bool.and_false]

/-- **Its claim is false at every size**: between every once and every leaky state the distance
exceeds `1/3`. -/
theorem tooSmallCert_false (m : ℕ) (j j' : Fin (m + 1)) :
    ((tooSmallCert m).cert.kernel ((tooSmallCert m).view (1, j)) ((tooSmallCert m).view (2, j')) : ℝ) <
      bisimulationMetric (realChain (blowup m)) (realChain (blowup m)) (discount : ℝ) (1, j) (2, j') := by
  rw [bisimulationMetric_blowup]
  exact tooSmall_wrong.trans_eq (bisimulationMetric_leak 1 2)

/-! ## The identity view on the leak chain -/

/-- The certificate on classes of the leak chain with the identity map. -/
def identityCert : OnClasses Unit Unit (Fin 4) (Fin 4) := ⟨id, leak, correct⟩

theorem identity_accepted : classCheck leak discount identityCert = true := by decide +kernel

/-- **Without classes the lumping check is pure overhead**: the same products, `16` more additions,
`20` more comparisons and `64` more tests than the incumbent. -/
theorem identity_work :
    classWork discount identityCert = (364, 320, 136, 79) ∧
      prefixpointWork leak discount correct = (364, 304, 116, 15) := by
  refine ⟨?_, quotientWork⟩
  unfold classWork
  rw [lumpWork_eq]
  change _ + prefixpointWork leak discount correct = _
  rw [quotientWork]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Controls
