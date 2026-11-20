import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Bounds

/-!
# The ambient check: no computable bound on all instances

The ambient check searches for a certificate on every instance. Read on the region of all instances,
the region theorem says:

* **a computable bound on all instances exists exactly when the property is decidable**
  (`boundedOn_univ_iff`; negated, `no_bound_iff`);
* **every computable bound is exceeded on infinitely many certified instances** of an undecidable
  property (`exceeded_infinite`): the certified instances all of whose certificates lie above the bound
  (`Exceeded`) form an infinite set. Were it finite, bounded search together with a finite table would
  decide the property.

The tree already has the global direction "a computable bound decides" for word certificates
(`Logic.ProofSearch.CertificateBounds.computableMeaning_of_bound`) and one missed positive
(`CertificateBounds.positive_requires_longer`); here the certificate is a number, as in
`CheckerTower.Certified`, the converse holds, and the missed instances are infinitely many.

**Instance:** halting on input zero, with the step index of bounded evaluation as certificate: no
computable function of the program bounds the step at which it halts (`halting_no_bound`), and every
computable candidate is exceeded by infinitely many halting programs (`halting_exceeded_infinite`).

**Control:** perfect squares are decidable and bounded by the instance (`Controls.square_decidable`);
the identity bound is exceeded nowhere (`Controls.square_exceeded_empty`), so "infinitely many" needs
undecidability.

**The budget regions.** At budget `k` the ambient search answers exactly the instances with a
certificate at most `k` (`budgetRegion`): a decidable region with the constant bound `k`
(`budgetRegion_bounded`). The budget regions grow with `k` (`budgetRegion_mono`) and together cover the
property (`budgetRegion_covers`); no single computable bound covers it when it is undecidable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open CheckerTower (Certified)
open Nat.Partrec

section Ambient

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- **Decided on all instances is decidable.** -/
theorem decidedOn_univ_iff : DecidedOn R (fun _ => true) ↔ ComputablePred (Certified R) := by
  rw [decidedOn_iff_computablePred R (Computable.const true)]
  constructor
  · intro decidable
    exact decidable.of_eq fun q => ⟨fun both => both.2, fun certified => ⟨rfl, certified⟩⟩
  · intro decidable
    exact decidable.of_eq fun q => ⟨fun certified => ⟨rfl, certified⟩, fun both => both.2⟩

/-- **The ambient theorem**: the search is computably bounded on all instances exactly when the
property is decidable. -/
theorem boundedOn_univ_iff (hR : Computable₂ R) :
    BoundedOn R (fun _ => true) ↔ ComputablePred (Certified R) :=
  (region_theorem R hR (Computable.const true)).trans (decidedOn_univ_iff R)

/-- **No computable bound on all instances exactly when the property is undecidable.** -/
theorem no_bound_iff (hR : Computable₂ R) :
    (¬ ∃ b : Q → ℕ, Computable b ∧ ∀ q, Certified R q → ∃ n ≤ b q, R n q = true) ↔
      ¬ ComputablePred (Certified R) := by
  rw [← boundedOn_univ_iff R hR]
  constructor
  · rintro noBound ⟨b, hb, bounds⟩
    exact noBound ⟨b, hb, fun q certified => bounds q rfl certified⟩
  · rintro noBound ⟨b, hb, bounds⟩
    exact noBound ⟨b, hb, fun q _ certified => bounds q certified⟩

/-- **The certified instances all of whose certificates exceed `b`.** -/
def Exceeded (b : Q → ℕ) : Set Q := {q | Certified R q ∧ ∀ n ≤ b q, R n q = false}

/-- **Every computable bound is exceeded on infinitely many certified instances** of an undecidable
property. -/
theorem exceeded_infinite (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R))
    {b : Q → ℕ} (hb : Computable b) : (Exceeded R b).Infinite := by
  classical
  intro finite
  apply undecidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun q => anyBelow R q (b q + 1) || decide (q ∈ finite.toFinset), ?_,
      funext fun q => propext ?_⟩
  · exact Primrec.or.to_comp.comp
      (computable_anyBelow R hR (m := fun q => b q + 1) ((Computable.succ.comp hb).of_eq fun _ => rfl))
      (computable_mem_finset finite.toFinset)
  · show Certified R q ↔ (anyBelow R q (b q + 1) || decide (q ∈ finite.toFinset)) = true
    rw [Bool.or_eq_true, decide_eq_true_iff, Set.Finite.mem_toFinset, anyBelow_iff]
    constructor
    · intro certified
      by_cases small : ∃ n < b q + 1, R n q = true
      · exact Or.inl small
      · refine Or.inr ?_
        show Certified R q ∧ ∀ n ≤ b q, R n q = false
        refine ⟨certified, fun n le => ?_⟩
        cases found : R n q with
        | false => rfl
        | true => exact absurd ⟨n, Nat.lt_succ_of_le le, found⟩ small
    · rintro (⟨n, _, found⟩ | member)
      · exact ⟨n, found⟩
      · exact member.1

/-! ## The budget regions of the ambient search -/

/-- **The budget region**: the instances with a certificate at most `k`. -/
def budgetRegion (k : ℕ) (q : Q) : Bool := anyBelow R q (k + 1)

theorem budgetRegion_computable (hR : Computable₂ R) (k : ℕ) : Computable (budgetRegion R k) :=
  computable_anyBelow R hR (m := fun _ => k + 1) (Computable.const _)

omit [Primcodable Q] in
theorem budgetRegion_bounds (k : ℕ) : BoundsOn R (budgetRegion R k) fun _ => k := by
  intro q inside _
  obtain ⟨n, lt, found⟩ := (anyBelow_iff R q (k + 1)).mp inside
  exact ⟨n, Nat.le_of_lt_succ lt, found⟩

/-- **A budget region is a decidable region with a constant bound.** -/
theorem budgetRegion_bounded (k : ℕ) : BoundedOn R (budgetRegion R k) :=
  ⟨fun _ => k, Computable.const k, budgetRegion_bounds R k⟩

omit [Primcodable Q] in
theorem budgetRegion_mono {k k' : ℕ} (le : k ≤ k') (q : Q) (inside : budgetRegion R k q = true) :
    budgetRegion R k' q = true := by
  obtain ⟨n, lt, found⟩ := (anyBelow_iff R q (k + 1)).mp inside
  exact (anyBelow_iff R q (k' + 1)).mpr ⟨n, by omega, found⟩

omit [Primcodable Q] in
/-- **The budget regions cover the property.** -/
theorem budgetRegion_covers {q : Q} (certified : Certified R q) : ∃ k, budgetRegion R k q = true := by
  obtain ⟨n, found⟩ := certified
  exact ⟨n, (anyBelow_iff R q (n + 1)).mpr ⟨n, Nat.lt_succ_self n, found⟩⟩

omit [Primcodable Q] in
/-- **The budget regions contain only certified instances.** -/
theorem certified_of_budgetRegion {k : ℕ} {q : Q} (inside : budgetRegion R k q = true) :
    Certified R q := by
  obtain ⟨n, _, found⟩ := (anyBelow_iff R q (k + 1)).mp inside
  exact ⟨n, found⟩

end Ambient

/-! ## Halting on input zero -/

/-- **No computable function of the program bounds the step at which it halts.** -/
theorem halting_no_bound :
    ¬ ∃ b : Code → ℕ, Computable b ∧ ∀ c, Certified haltR c → ∃ n ≤ b c, haltR n c = true :=
  (no_bound_iff haltR haltR_computable).mpr not_computablePred_haltR

/-- **Every computable candidate bound is exceeded by infinitely many halting programs.** -/
theorem halting_exceeded_infinite {b : Code → ℕ} (hb : Computable b) : (Exceeded haltR b).Infinite :=
  exceeded_infinite haltR haltR_computable not_computablePred_haltR hb

theorem mem_exceeded_haltR {b : Code → ℕ} {c : Code} :
    c ∈ Exceeded haltR b ↔ (Code.eval c 0).Dom ∧ ∀ n ≤ b c, Code.evaln n c 0 = Option.none := by
  show (Certified haltR c ∧ ∀ n ≤ b c, haltR n c = false) ↔ _
  rw [certified_haltR_iff]
  refine and_congr Iff.rfl (forall_congr' fun n => imp_congr_right fun _ => ?_)
  show (Code.evaln n c 0).isSome = false ↔ _
  rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

/-! ## Controls -/

namespace Controls

/-- **Control: perfect squares are decidable**, by the bound of the instance. -/
theorem square_decidable : ComputablePred (Certified squareR) :=
  (boundedOn_univ_iff squareR squareR_computable).mp square_boundedOn

/-- **Control: the identity bound is exceeded nowhere** on a decidable property. -/
theorem square_exceeded_empty : Exceeded squareR id = ∅ := by
  ext q
  constructor
  · rintro ⟨certified, beyond⟩
    obtain ⟨n, le, found⟩ := square_bounds q rfl certified
    rw [beyond n le] at found
    exact Bool.noConfusion found
  · intro member
    exact absurd member (Set.notMem_empty q)

/-- Control: at budget `3` the ambient search for a square answers `9`, at budget `2` it does not. -/
theorem square_budget : budgetRegion squareR 3 9 = true ∧ budgetRegion squareR 2 9 = false := by
  decide

end Controls

#print axioms decidedOn_univ_iff
#print axioms boundedOn_univ_iff
#print axioms no_bound_iff
#print axioms exceeded_infinite
#print axioms budgetRegion_computable
#print axioms budgetRegion_bounds
#print axioms budgetRegion_bounded
#print axioms budgetRegion_mono
#print axioms budgetRegion_covers
#print axioms certified_of_budgetRegion
#print axioms halting_no_bound
#print axioms halting_exceeded_infinite
#print axioms mem_exceeded_haltR
#print axioms Controls.square_decidable
#print axioms Controls.square_exceeded_empty
#print axioms Controls.square_budget

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
