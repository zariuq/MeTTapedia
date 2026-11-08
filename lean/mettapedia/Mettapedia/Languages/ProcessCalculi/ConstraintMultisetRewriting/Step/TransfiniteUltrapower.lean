import Mathlib.Order.Filter.FilterProduct
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Charge

/-!
# Hyperfinite runs: conserved charges through an ultrapower

A **hyperfinite run** (`HyperRun`) is a family of runs of a step, one at each index, read modulo an
ultrafilter `U`: its length (`HyperRun.length`), its potentials at the start and the end, and what it
takes and makes are germs along `U`, elements of the ultrapowers of `ℕ` and of the charge's monoid.

* **Conservation** (`HyperRun.balance`): for every conserved charge, the potential at the end of the
  hyperfinite run plus everything it took is the potential at its start plus everything it made, in
  the ultrapower. In particular for the occurrence weights of every step (`HyperRun.balance_weight`).
* **Balanced firings** (`HyperRun.endPotential_eq_of_balanced`): when `U`-almost every coordinate
  balances at each firing, the potential germ is constant.
* **The fold filter transfers** (`HyperRun.eventually_not_fold`): when the hyperfinite run does not
  take what it makes, `U`-almost every coordinate run fails to fold back to its start. This uses that
  `U` is an ultrafilter: an inequality of germs is an inequality at `U`-almost every index
  (`germ_ne_iff`, Łoś for a negated equation). Conversely, if `U`-almost every coordinate folds, the
  hyperfinite run takes what it makes (`HyperRun.taken_eq_made_of_eventually_fold`).
* **Infinite length** (`HyperRun.const_lt_length`): if `U` is free and only finitely many coordinate
  runs have length at most `n`, for every `n`, then the length exceeds every standard number.

**Control.** Over the cofinite filter, which is not an ultrafilter, germs can differ without differing
eventually: the indicator of the evens and `0` (`cofinite_germ_ne_not_eventually_ne`). That is why the
fold filter transfers through an ultrapower and not through a reduced power.

This is a bridge, not a foundation: a hyperfinite run is assembled from finite coordinate runs. A
germ has no coordinates of its own; what can be read from it is what holds on a set in `U`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uA uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

open Filter

/-- **Łoś for a negated equation**: along an ultrafilter, germs differ exactly when the functions
differ almost everywhere. -/
theorem germ_ne_iff {I : Type uI} {B : Type uA} (U : Ultrafilter I) (f g : I → B) :
    (f : Germ (U : Filter I) B) ≠ g ↔ ∀ᶠ i in (U : Filter I), f i ≠ g i := by
  rw [Ne, Germ.coe_eq, Ultrafilter.eventually_not]
  rfl

/-- **A hyperfinite run**: a run at each index. -/
structure HyperRun (P : Step X O State Firing) (I : Type uI) where
  start : I → State
  run : ∀ i, P.Run (start i)

namespace HyperRun

variable {P : Step X O State Firing} {I : Type uI} (R : HyperRun P I) (U : Ultrafilter I)
  {A : Type uA} [AddCommMonoid A] (Q : ConservedCharge P A)

/-- **The length**, a hypernatural. -/
def length : Germ (U : Filter I) ℕ := ↑fun i => (R.run i).word.length

/-- The potential at the start. -/
def startPotential : Germ (U : Filter I) A := ↑fun i => Q.potential (R.start i)

/-- The potential at the end. -/
def endPotential : Germ (U : Filter I) A := ↑fun i => Q.potential (R.run i).last

/-- Everything taken. -/
def taken : Germ (U : Filter I) A := ↑fun i => Q.runTaken (R.run i)

/-- Everything made. -/
def made : Germ (U : Filter I) A := ↑fun i => Q.runMade (R.run i)

/-- **Conservation along the hyperfinite run.** -/
theorem balance :
    R.endPotential U Q + R.taken U Q = R.startPotential U Q + R.made U Q := by
  unfold endPotential taken startPotential made
  rw [← Germ.coe_add, ← Germ.coe_add]
  exact congrArg _ (funext fun i => Q.run_balance (R.run i))

/-- Conservation for the occurrence weights of every step. -/
theorem balance_weight (w : O → A) :
    R.endPotential U (weightCharge P w) + R.taken U (weightCharge P w) =
      R.startPotential U (weightCharge P w) + R.made U (weightCharge P w) :=
  R.balance U _

/-- **Balanced firings keep the potential germ constant.** -/
theorem endPotential_eq_of_balanced [IsRightCancelAdd A]
    (balanced : ∀ᶠ i in (U : Filter I), ∀ x ∈ (R.run i).word, Q.taken x.1 x.2 = Q.made x.1 x.2) :
    R.endPotential U Q = R.startPotential U Q :=
  Germ.coe_eq.mpr (balanced.mono fun i => Q.potential_last_of_balanced (R.run i))

/-- **If almost every coordinate folds, the hyperfinite run takes what it makes.** -/
theorem taken_eq_made_of_eventually_fold [IsLeftCancelAdd A] {T : Transport P}
    (invariant : Q.Invariant T)
    (folds : ∀ᶠ i in (U : Filter I), T.Same (R.start i) (R.run i).last) :
    R.taken U Q = R.made U Q :=
  Germ.coe_eq.mpr (folds.mono fun i fold => ConservedCharge.balanced_of_fold invariant (R.run i) fold)

/-- **The fold filter transfers**: a hyperfinite run that does not take what it makes has almost
every coordinate run failing to fold. -/
theorem eventually_not_fold [IsLeftCancelAdd A] {T : Transport P} (invariant : Q.Invariant T)
    (unbalanced : R.taken U Q ≠ R.made U Q) :
    ∀ᶠ i in (U : Filter I), ¬ T.Same (R.start i) (R.run i).last :=
  ((germ_ne_iff U _ _).mp unbalanced).mono fun i differ =>
    ConservedCharge.not_fold_of_unbalanced invariant (R.run i) differ

/-- **Infinite length**: along a free ultrafilter, if only finitely many coordinate runs have length
at most `n`, for every `n`, the length exceeds every standard number. -/
theorem const_lt_length (free : (U : Filter I) ≤ cofinite)
    (unbounded : ∀ n : ℕ, {i | (R.run i).word.length ≤ n}.Finite) (n : ℕ) :
    (n : Germ (U : Filter I) ℕ) < R.length U := by
  show ((fun _ : I => n : I → ℕ) : Germ (U : Filter I) ℕ) < ↑fun i => (R.run i).word.length
  rw [Germ.coe_lt]
  refine free (Filter.mem_cofinite.mpr ?_)
  refine (unbounded n).subset fun i outside => ?_
  simpa using outside

end HyperRun

/-! ## Control: a reduced power is not enough -/

/-- The indicator of the evens. -/
def evenIndicator (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 0

/-- **Over the cofinite filter, germs can differ without differing eventually.** -/
theorem cofinite_germ_ne_not_eventually_ne :
    (evenIndicator : Germ (cofinite : Filter ℕ) ℕ) ≠ (fun _ => 0 : ℕ → ℕ) ∧
      ¬ ∀ᶠ n in (cofinite : Filter ℕ), evenIndicator n ≠ 0 := by
  have evens : {n : ℕ | n % 2 = 0}.Infinite :=
    Set.infinite_of_forall_exists_gt fun n => ⟨2 * n + 2, by simp [Nat.mul_mod_right], by omega⟩
  have odds : {n : ℕ | n % 2 = 1}.Infinite :=
    Set.infinite_of_forall_exists_gt fun n => ⟨2 * n + 1, by simp [Nat.add_mod], by omega⟩
  refine ⟨fun same => ?_, fun eventually => ?_⟩
  · have := Germ.coe_eq.mp same
    rw [EventuallyEq, eventually_cofinite] at this
    exact evens (this.subset fun n even => by simp [evenIndicator, even.out])
  · rw [eventually_cofinite] at eventually
    exact odds (eventually.subset fun n odd => by
      have : n % 2 = 1 := odd
      simp [evenIndicator, this])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Interface.germ_ne_iff
#print axioms Interface.HyperRun.balance
#print axioms Interface.HyperRun.balance_weight
#print axioms Interface.HyperRun.endPotential_eq_of_balanced
#print axioms Interface.HyperRun.taken_eq_made_of_eventually_fold
#print axioms Interface.HyperRun.eventually_not_fold
#print axioms Interface.HyperRun.const_lt_length
#print axioms Interface.cofinite_germ_ne_not_eventually_ne

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
