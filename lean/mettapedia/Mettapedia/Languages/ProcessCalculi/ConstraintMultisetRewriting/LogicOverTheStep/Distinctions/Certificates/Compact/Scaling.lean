import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Work

/-!
# Where certifying on classes wins, for every chain

**Upper bound** (`coveredWork_all_le`, `prefixpointWork_all_le`, `classWork_all_le`): on every branch,
one action at one pair of a prefixpoint certificate over `k` states costs at most `5k² + 3k + 5`
counted operations; so checking any certificate on `k` classes of a chain with `n` states costs at most

  `|A| n² (k + 1) + |A| n k + |Atom| n + 3k² + 4 |Atom| k² + |A| k² (5k² + 3k + 5)`,

whether it is accepted or not, and whatever its masses.

**Lower bound** (`prefixpointWork_lower`): every accepted prefixpoint certificate of the chain costs at
least `|A| n(n-1)(n² + 1)` products and `|A| n(n-1)(n² + n)` additions.

**So** (`four_times_cheaper_of_large`): whenever four times the upper bound is at most the lower bound,
the certificate on classes is at least four times cheaper to check than every accepted prefixpoint
certificate. The upper bound is quadratic in `n` and the lower bound quartic: the gain grows with the
number of states per class, and it is lost when `n` is close to `k`. With one action, one observation
and four classes the condition holds from nine states on (`four_classes_from_nine`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

/-- **One action at one pair costs at most `5n² + 3n + 5` counted operations**, on every branch. -/
theorem coveredWork_all_le (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cost bound : S → S → ℚ)
    (listed : A → S → S → Option (S → S → ℚ)) (a : A) (s t : S) :
    (coveredWork P c cost bound listed a s t).all ≤
      5 * (Fintype.card S * Fintype.card S) + 3 * Fintype.card S + 5 := by
  have square := Nat.zero_le (Fintype.card S * Fintype.card S)
  unfold coveredWork
  rcases listed a s t with _ | θ
  · dsimp only
    split_ifs
    · simp only [Work.all, testWork, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
      omega
    · rcases listed a t s with _ | θ'
      · simp only [Work.all, testWork, productWork, stepWork, Prod.fst_add, Prod.snd_add]
        linarith
      · dsimp only
        split_ifs
        · simp only [Work.all, testWork, jointWork, stepWork, Prod.fst_add, Prod.snd_add,
            Prod.fst_zero, Prod.snd_zero]
          linarith
        · simp only [Work.all, testWork, jointWork, productWork, stepWork, Prod.fst_add,
            Prod.snd_add]
          linarith
  · dsimp only
    split_ifs
    · simp only [Work.all, tableWork, jointWork, stepWork, Prod.fst_add, Prod.snd_add]
      linarith
    · simp only [Work.all, tableWork]
      linarith

/-- **A prefixpoint certificate over `k` states costs at most
`3k² + 4 |Atom| k² + |A| k² (5k² + 3k + 5)` counted operations.** -/
theorem prefixpointWork_all_le [Fintype A] [Fintype Atom] (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (cert : Prefixpoint A S) :
    (prefixpointWork P c cert).all ≤
      3 * (Fintype.card S * Fintype.card S) +
        4 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)) +
        Fintype.card A * (Fintype.card S * Fintype.card S) *
          (5 * (Fintype.card S * Fintype.card S) + 3 * Fintype.card S + 5) := by
  set K := 5 * (Fintype.card S * Fintype.card S) + 3 * Fintype.card S + 5
  have sum : (∑ a, ∑ s, ∑ t, coveredWork P c cert.kernel cert.kernel cert.listed a s t).all ≤
      Fintype.card A * (Fintype.card S * Fintype.card S) * K := by
    have split : ∀ w : A → S → S → Work, (∑ a, ∑ s, ∑ t, w a s t).all =
        ∑ a, ∑ s, ∑ t, (w a s t).all := by
      intro w
      simp only [Work.all, Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
    rw [split]
    calc ∑ a, ∑ s, ∑ t, (coveredWork P c cert.kernel cert.kernel cert.listed a s t).all
        ≤ ∑ _a : A, ∑ _s : S, ∑ _t : S, K :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
            coveredWork_all_le P c cert.kernel cert.kernel cert.listed a s t
      _ = Fintype.card A * (Fintype.card S * Fintype.card S) * K := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have parts : (prefixpointWork P c cert).all =
      Fintype.card S * Fintype.card S + 4 * (Fintype.card Atom * (Fintype.card S * Fintype.card S)) +
        (∑ a, ∑ s, ∑ t, coveredWork P c cert.kernel cert.kernel cert.listed a s t).all +
        2 * (Fintype.card S * Fintype.card S) := by
    simp only [prefixpointWork, Work.all, Prod.fst_add, Prod.snd_add]
    ring
  rw [parts]
  linarith

omit [DecidableEq S] in
/-- **Checking any certificate on `k` classes of a chain with `n` states costs at most**
`|A| n² (k + 1) + |A| n k + |Atom| n + 3k² + 4 |Atom| k² + |A| k² (5k² + 3k + 5)`. -/
theorem classWork_all_le [Fintype A] [Fintype Atom] (c : ℚ) (cert : OnClasses A Atom S C) :
    (classWork c cert).all ≤
      Fintype.card A * (Fintype.card S * Fintype.card S) * (Fintype.card C + 1) +
        Fintype.card A * (Fintype.card S * Fintype.card C) + Fintype.card Atom * Fintype.card S +
        (3 * (Fintype.card C * Fintype.card C) +
          4 * (Fintype.card Atom * (Fintype.card C * Fintype.card C)) +
          Fintype.card A * (Fintype.card C * Fintype.card C) *
            (5 * (Fintype.card C * Fintype.card C) + 3 * Fintype.card C + 5)) := by
  have quotient := prefixpointWork_all_le cert.quotient c cert.cert
  have lump := lumpWork_eq (C := C) A Atom cert.view
  have parts : (classWork c cert).all = (lumpWork A Atom cert.view).all +
      (prefixpointWork cert.quotient c cert.cert).all := by
    simp only [classWork, Work.all, Prod.fst_add, Prod.snd_add]
    ring
  have lumpAll : (lumpWork A Atom cert.view).all =
      Fintype.card A * (Fintype.card S * Fintype.card S) * (Fintype.card C + 1) +
        Fintype.card A * (Fintype.card S * Fintype.card C) + Fintype.card Atom * Fintype.card S := by
    rw [lump]
    simp only [Work.all]
    ring
  rw [parts, lumpAll]
  exact Nat.add_le_add_left quotient _

/-- **Four times cheaper, for every chain large enough against its classes**: if four times the upper
bound on the class certificate's work is at most the lower bound on every accepted prefixpoint
certificate's products and additions, the class certificate is at least four times cheaper. -/
theorem four_times_cheaper_of_large [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S}
    {c : ℚ} {cert : Prefixpoint A S} (accepted : check P c cert = true)
    (classes : OnClasses A Atom S C)
    (large : 4 * (Fintype.card A * (Fintype.card S * Fintype.card S) * (Fintype.card C + 1) +
        Fintype.card A * (Fintype.card S * Fintype.card C) + Fintype.card Atom * Fintype.card S +
        (3 * (Fintype.card C * Fintype.card C) +
          4 * (Fintype.card Atom * (Fintype.card C * Fintype.card C)) +
          Fintype.card A * (Fintype.card C * Fintype.card C) *
            (5 * (Fintype.card C * Fintype.card C) + 3 * Fintype.card C + 5))) ≤
      Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) *
        (Fintype.card S * Fintype.card S + 1))) +
      Fintype.card A * (Fintype.card S * ((Fintype.card S - 1) *
        (Fintype.card S * Fintype.card S + Fintype.card S)))) :
    4 * (classWork c classes).all ≤ (prefixpointWork P c cert).1 + (prefixpointWork P c cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  have upper := classWork_all_le c classes
  omega

/-- **With one action, one observation and four classes, the condition holds from nine states on.** -/
theorem four_classes_from_nine (n : ℕ) (nine : 9 ≤ n) :
    4 * (1 * (n * n) * (4 + 1) + 1 * (n * 4) + 1 * n +
        (3 * (4 * 4) + 4 * (1 * (4 * 4)) + 1 * (4 * 4) * (5 * (4 * 4) + 3 * 4 + 5))) ≤
      1 * (n * ((n - 1) * (n * n + 1))) + 1 * (n * ((n - 1) * (n * n + n))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  rw [show k + 9 - 1 = k + 8 by omega]
  nlinarith [Nat.zero_le k, Nat.zero_le (k * k), Nat.zero_le (k * k * k), Nat.zero_le (k * k * k * k)]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
