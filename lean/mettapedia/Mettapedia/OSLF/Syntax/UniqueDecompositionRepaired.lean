import Mettapedia.OSLF.Syntax.UniqueDecompositionFails
import Mettapedia.OSLF.Syntax.NormalFormStrength

/-!
# Unique decomposition, with the hypothesis that makes it true

The weaker disjoint-predicate statement fails: it constrains which processes
each side accepts, but not how a composite may be partitioned. The full source
proposition additionally requires name-based grade-zero separation, which the
counterexample does not establish.

The hypothesis that does the work is disjointness of **prime support**.  Fix two
disjoint sets of primes and let each predicate accept exactly the processes all
of whose primes lie in its own set.  Then every prime of a composite is forced to
one side and the split is unique in this free commutative-monoid example. No
description-length or runtime-cost additivity theorem is established here.

In this language the primes are the outputs, so a process is determined up to
structural congruence by how many outputs it carries on each channel.  That is
proved here in both directions -- the count is invariant (in the counterexample
module) and it is complete (here) -- which is unique decomposition into primes
for this monoid, and is what the corrected proposition rests on.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

namespace ParallelFragment

/-! ## The commutative-monoid interface

Three closed instances of the axioms and the congruence rule.  Everything below
is derived from these four facts and nothing else, so the argument is about the
monoid and not about the particular signature. -/

def nulT : Term psig [] PSrt.proc := Term.op (S := psig) POp.nul Args.nil

def sub1 (a : Term psig [] PSrt.proc) :
    (s : PSrt) → Var [PSrt.proc] s → Term psig [] s
  | _, .zero => a
  | _, .succ v => nomatch v

def sub2 (a b : Term psig [] PSrt.proc) :
    (s : PSrt) → Var [PSrt.proc, PSrt.proc] s → Term psig [] s
  | _, .zero => a
  | _, .succ .zero => b
  | _, .succ (.succ v) => nomatch v

def sub3 (a b c : Term psig [] PSrt.proc) :
    (s : PSrt) → Var [PSrt.proc, PSrt.proc, PSrt.proc] s → Term psig [] s
  | _, .zero => a
  | _, .succ .zero => b
  | _, .succ (.succ .zero) => c
  | _, .succ (.succ (.succ v)) => nomatch v

/-- Parallel composition is a congruence. -/
theorem parCong {a a' b b' : Term psig [] PSrt.proc}
    (ha : EqClosure ac1 a a') (hb : EqClosure ac1 b b') :
    EqClosure ac1 (parT a b) (parT a' b') := by
  show EqClosure ac1 (Term.op (S := psig) POp.par (.cons a (.cons b .nil)))
    (Term.op (S := psig) POp.par (.cons a' (.cons b' .nil)))
  refine EqClosure.cong (S := psig) POp.par ?_
  exact .cons ha (.cons hb .nil)

theorem parComm (a b : Term psig [] PSrt.proc) :
    EqClosure ac1 (parT a b) (parT b a) := by
  have h : EqClosure ac1 (bind (sub2 a b) (instantiate emptyBody commAx.lhs))
      (bind (sub2 a b) (instantiate emptyBody commAx.rhs)) :=
    EqClosure.ax (E := ac1) (Γ := ([] : Ctx psig)) ⟨0, by decide⟩ emptyBody (sub2 a b)
  simpa only [commAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
    sub2, parT] using h

theorem parAssoc (a b c : Term psig [] PSrt.proc) :
    EqClosure ac1 (parT (parT a b) c) (parT a (parT b c)) := by
  have h : EqClosure ac1 (bind (sub3 a b c) (instantiate emptyBody assocAx.lhs))
      (bind (sub3 a b c) (instantiate emptyBody assocAx.rhs)) :=
    EqClosure.ax (E := ac1) (Γ := ([] : Ctx psig)) ⟨1, by decide⟩ emptyBody (sub3 a b c)
  simpa only [assocAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
    sub3, parT] using h

theorem parUnitR (a : Term psig [] PSrt.proc) :
    EqClosure ac1 (parT a nulT) a := by
  have h : EqClosure ac1 (bind (sub1 a) (instantiate emptyBody unitAx.lhs))
      (bind (sub1 a) (instantiate emptyBody unitAx.rhs)) :=
    EqClosure.ax (E := ac1) (Γ := ([] : Ctx psig)) ⟨2, by decide⟩ emptyBody (sub1 a)
  simpa only [unitAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
    sub1, parT, nulT] using h

theorem parUnitL (a : Term psig [] PSrt.proc) :
    EqClosure ac1 (parT nulT a) a :=
  EqClosure.trans (parComm nulT a) (parUnitR a)

/-- The middle-exchange law, derived: it is what lets two factorizations be
compared componentwise. -/
theorem parSwap4 (p q r s : Term psig [] PSrt.proc) :
    EqClosure ac1 (parT (parT p q) (parT r s)) (parT (parT p r) (parT q s)) :=
  EqClosure.trans (parAssoc p q (parT r s))
    (EqClosure.trans
      (parCong (EqClosure.refl p)
        (EqClosure.trans (EqClosure.symm (parAssoc q r s))
          (EqClosure.trans (parCong (parComm q r) (EqClosure.refl s))
            (parAssoc r q s))))
      (EqClosure.symm (parAssoc p r (parT q s))))

/-- The count is additive over parallel composition. -/
theorem countOut_par (n : Fin 3) (x y : Term psig [] PSrt.proc) :
    countOut n (parT x y) = countOut n x + countOut n y := by
  simp only [parT, countOut, countOutArgs, headCount]
  omega

/-! ## Prime powers and the normal form -/

/-- `k` copies of the output on channel `n`. -/
def pow (n : Fin 3) : Nat → Term psig [] PSrt.proc
  | 0 => nulT
  | k + 1 => parT (u n) (pow n k)

/-- The normal form at a given multiplicity for each prime. -/
def rep (a b c : Nat) : Term psig [] PSrt.proc :=
  parT (pow 0 a) (parT (pow 1 b) (pow 2 c))

theorem pow_add (n : Fin 3) (j k : Nat) :
    EqClosure ac1 (parT (pow n j) (pow n k)) (pow n (j + k)) := by
  induction j with
  | zero => simpa only [Nat.zero_add, pow] using parUnitL (pow n k)
  | succ j ih =>
      have hstep : EqClosure ac1 (parT (parT (u n) (pow n j)) (pow n k))
          (parT (u n) (pow n (j + k))) :=
        EqClosure.trans (parAssoc (u n) (pow n j) (pow n k))
          (parCong (EqClosure.refl (u n)) ih)
      simpa only [pow, Nat.succ_add] using hstep

/-- **The normal forms compose**: the monoid structure is transported to the
multiplicity vectors. -/
theorem rep_add (a b c a' b' c' : Nat) :
    EqClosure ac1 (parT (rep a b c) (rep a' b' c'))
      (rep (a + a') (b + b') (c + c')) := by
  refine EqClosure.trans (parSwap4 (pow 0 a) (parT (pow 1 b) (pow 2 c))
    (pow 0 a') (parT (pow 1 b') (pow 2 c'))) ?_
  refine EqClosure.trans (parCong (EqClosure.refl _)
    (parSwap4 (pow 1 b) (pow 2 c) (pow 1 b') (pow 2 c'))) ?_
  exact parCong (pow_add 0 a a')
    (parCong (pow_add 1 b b') (pow_add 2 c c'))

/-! ## Every process is its normal form -/

theorem countOut_pow (m n : Fin 3) (k : Nat) :
    countOut m (pow n k) = if m = n then k else 0 := by
  induction k with
  | zero => simp only [pow, nulT, countOut, countOutArgs, headCount]; split <;> rfl
  | succ k ih =>
      simp only [pow, parT, u, countOut, countOutArgs, headCount, ih]
      split <;> omega

theorem countOut_rep (m : Fin 3) (a b c : Nat) :
    countOut m (rep a b c)
      = (if m = 0 then a else 0) + ((if m = 1 then b else 0) + (if m = 2 then c else 0)) := by
  simp only [rep, parT, countOut, countOutArgs, headCount, countOut_pow]
  omega

/-- A single output is its own normal form, channel by channel. -/
theorem to_rep_out : ∀ n : Fin 3,
    EqClosure ac1 (u n) (rep (countOut 0 (u n)) (countOut 1 (u n)) (countOut 2 (u n)))
  | ⟨0, _⟩ => by
      show EqClosure ac1 (u 0) (rep 1 0 0)
      refine EqClosure.symm ?_
      show EqClosure ac1 (parT (parT (u 0) nulT) (parT nulT nulT)) (u 0)
      exact EqClosure.trans (parCong (parUnitR (u 0)) (parUnitR nulT))
        (parUnitR (u 0))
  | ⟨1, _⟩ => by
      show EqClosure ac1 (u 1) (rep 0 1 0)
      refine EqClosure.symm ?_
      show EqClosure ac1 (parT nulT (parT (parT (u 1) nulT) nulT)) (u 1)
      exact EqClosure.trans (parUnitL (parT (parT (u 1) nulT) nulT))
        (EqClosure.trans (parUnitR (parT (u 1) nulT)) (parUnitR (u 1)))
  | ⟨2, _⟩ => by
      show EqClosure ac1 (u 2) (rep 0 0 1)
      refine EqClosure.symm ?_
      show EqClosure ac1 (parT nulT (parT nulT (parT (u 2) nulT))) (u 2)
      exact EqClosure.trans (parUnitL (parT nulT (parT (u 2) nulT)))
        (EqClosure.trans (parUnitL (parT (u 2) nulT)) (parUnitR (u 2)))
  | ⟨_ + 3, h⟩ => by omega

/-- **Completeness of the count.**  Every process is structurally congruent to
the normal form its own counts name, so the counts determine the class. -/
theorem to_rep_bounded : ∀ (k : Nat) (t : Term psig [] PSrt.proc), termSize t ≤ k →
    EqClosure ac1 t (rep (countOut 0 t) (countOut 1 t) (countOut 2 t)) := by
  intro k
  induction k with
  | zero =>
      intro t ht
      exact absurd (Nat.lt_of_lt_of_le (termSize_pos t) ht) (by omega)
  | succ k ih =>
      intro t ht
      match t with
      | .var v => exact nomatch v
      | .op POp.nul .nil =>
          show EqClosure ac1 nulT (rep 0 0 0)
          refine EqClosure.symm ?_
          show EqClosure ac1 (parT nulT (parT nulT nulT)) nulT
          exact EqClosure.trans (parUnitL (parT nulT nulT)) (parUnitR nulT)
      | .op (POp.out n) .nil => exact to_rep_out n
      | .op POp.par (.cons x (.cons y .nil)) =>
          have hsz : termSize x + termSize y + 1 ≤ k + 1 := by
            simpa only [termSize, argsSize, Nat.add_zero] using ht
          have hx := ih x (by omega)
          have hy := ih y (by omega)
          show EqClosure ac1 (parT x y)
            (rep (countOut 0 (parT x y)) (countOut 1 (parT x y)) (countOut 2 (parT x y)))
          rw [countOut_par, countOut_par, countOut_par]
          exact EqClosure.trans (parCong hx hy)
            (rep_add (countOut 0 x) (countOut 1 x) (countOut 2 x)
              (countOut 0 y) (countOut 1 y) (countOut 2 y))

theorem to_rep (t : Term psig [] PSrt.proc) :
    EqClosure ac1 t (rep (countOut 0 t) (countOut 1 t) (countOut 2 t)) :=
  to_rep_bounded (termSize t) t (Nat.le_refl _)

/-- **The count is a complete invariant.**  Two processes with the same prime
multiplicities are structurally congruent.  With `countOut_invariant` this is
unique decomposition into primes for this monoid. -/
theorem eq_of_countOut_eq {t u' : Term psig [] PSrt.proc}
    (h : ∀ n : Fin 3, countOut n t = countOut n u') : EqClosure ac1 t u' := by
  have ht := to_rep t
  rw [h 0, h 1, h 2] at ht
  exact EqClosure.trans ht (EqClosure.symm (to_rep u'))

/-! ## The corrected proposition -/

/-- A predicate with prime support `A`: every prime of the process lies in `A`.
Unlike disjointness of predicate extensions alone, this constrains prime support
and forces
each prime to a determined side of a split. -/
def SupportedBy (A : Fin 3 → Prop) (t : Term psig [] PSrt.proc) : Prop :=
  ∀ n : Fin 3, ¬ A n → countOut n t = 0

/-- Support is a property of congruence classes. -/
theorem supportedBy_congruent {A : Fin 3 → Prop} {t t' : Term psig [] PSrt.proc}
    (he : EqClosure ac1 t t') (h : SupportedBy A t) : SupportedBy A t' := by
  intro n hn
  rw [← countOut_invariant n he]
  exact h n hn

/-- **Unique decomposition, corrected.**  If the two predicates have disjoint
prime supports that between them cover the primes, then a composite determines
each half up to structural congruence.  Both halves, not merely the composite. -/
theorem unique_decomposition_of_disjoint_support
    {A B : Fin 3 → Prop}
    (hdisj : ∀ n, ¬ (A n ∧ B n)) (hcover : ∀ n, A n ∨ B n)
    {p q p' q' : Term psig [] PSrt.proc}
    (hsplit : EqClosure ac1 (parT p q) (parT p' q'))
    (hp : SupportedBy A p) (hp' : SupportedBy A p')
    (hq : SupportedBy B q) (hq' : SupportedBy B q') :
    EqClosure ac1 p p' ∧ EqClosure ac1 q q' := by
  have hsum : ∀ n : Fin 3,
      countOut n p + countOut n q = countOut n p' + countOut n q' := by
    intro n
    have h := countOut_invariant n hsplit
    simp only [parT, countOut, countOutArgs, headCount] at h
    omega
  have hpp : ∀ n : Fin 3, countOut n p = countOut n p' := by
    intro n
    rcases hcover n with hA | hB
    · have h1 : countOut n q = 0 := hq n (fun hB => hdisj n ⟨hA, hB⟩)
      have h2 : countOut n q' = 0 := hq' n (fun hB => hdisj n ⟨hA, hB⟩)
      have := hsum n
      omega
    · have h1 : countOut n p = 0 := hp n (fun hA => hdisj n ⟨hA, hB⟩)
      have h2 : countOut n p' = 0 := hp' n (fun hA => hdisj n ⟨hA, hB⟩)
      omega
  have hqq : ∀ n : Fin 3, countOut n q = countOut n q' := by
    intro n
    have := hsum n
    have := hpp n
    omega
  exact ⟨eq_of_countOut_eq hpp, eq_of_countOut_eq hqq⟩

/-! ## Disjoint extensions alone are strictly weaker

A control tying the two results together: the predicates of the counterexample
have disjoint extensions, and one of them is not supported by any set disjoint
from the other's -- which is exactly the gap the corrected hypothesis closes. -/

/-- `phi` is not closed under dropping a prime from its support: it accepts a
process with an `out 1` and also one without, so no prime set both supports it
and forces the split.  This is why disjoint extensions were not enough. -/
theorem phi_is_not_support_closed :
    phi (u 0) ∧ phi (parT (u 0) (u 1))
      ∧ countOut 1 (u 0) ≠ countOut 1 (parT (u 0) (u 1)) := by
  refine ⟨split_left.1, split_right.1, ?_⟩
  simp [u, parT, countOut, countOutArgs, headCount]

/-- And under the corrected hypothesis the counterexample cannot be built: the
two halves it produces are forced to be congruent. -/
theorem corrected_hypothesis_excludes_the_counterexample
    {A B : Fin 3 → Prop} (hdisj : ∀ n, ¬ (A n ∧ B n)) (hcover : ∀ n, A n ∨ B n)
    (hp : SupportedBy A (u 0)) (hp' : SupportedBy A (parT (u 0) (u 1)))
    (hq : SupportedBy B (parT (u 1) (u 2))) (hq' : SupportedBy B (u 2)) :
    False :=
  halves_differ
    ((unique_decomposition_of_disjoint_support hdisj hcover
      (EqClosure.symm same_process) hp hp' hq hq').1)

/-! ## What the count is, in the general vocabulary

The two halves above are soundness and completeness of a section of the quotient
by the structural equations, which is what a canonical form *for a theory* means
-- as opposed to a normal form for a rewrite system, which is canonical only for
its own conversion.  Exhibiting it as one connects this fragment to the general
notion rather than leaving the two beside each other. -/

/-- **The count is a canonical form for the structural equations.**  `to_rep` is
its soundness and `countOut_invariant` its completeness, so the repaired
decomposition is a section of the quotient and not merely a pair of lemmas. -/
def parallelNF :
    Mettapedia.OSLF.Syntax.NormalFormStrength.SemanticNF
      (fun t u : Term psig [] PSrt.proc => EqClosure ac1 t u) where
  rep t := rep (countOut 0 t) (countOut 1 t) (countOut 2 t)
  sound := to_rep
  complete t u h := by
    rw [countOut_invariant 0 h, countOut_invariant 1 h, countOut_invariant 2 h]

end ParallelFragment

end Mettapedia.OSLF.Binding
