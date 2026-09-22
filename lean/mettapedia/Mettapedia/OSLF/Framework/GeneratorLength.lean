import Mettapedia.OSLF.Formula
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Choose.Basic

/-!
# Generator length against the size of what is generated

The point of carrying a generator in the formula language, rather than a
monotone transformer beside it, is that a generator has *symbols*.  This module
exhibits the two quantities that then exist and shows they do not move
together: a five-symbol formula whose extension is an infinite region, and the
counting law under which a description that grows by a constant describes a
region that grows by a square.

Nothing here is a definition schema: the formula is written down, its symbol
count, closedness and positivity are read off by computation, its extension is
characterised exactly, and the executable checker is run on it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneratorLength

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula

/-! ## A generator and its extension -/

/-- The body of the generator: observed here, or one step from somewhere it
holds.  The bound variable is index zero. -/
def reachableBody (atom : String) : OSLFFormula :=
  .or (.atom atom) (.dia (.var 0))

/-- `µX. (a ∨ ◇X)`. -/
def reachable (atom : String) : OSLFFormula := .mu (reachableBody atom)

/-- Five symbols, whatever the observation and whatever the system. -/
theorem reachable_size (atom : String) : OSLFFormula.size (reachable atom) = 5 := rfl

/-- The body has exactly the one free scope variable its binder provides. -/
theorem reachableBody_closedAt (atom : String) :
    OSLFFormula.closedAt 1 (reachableBody atom) = true := rfl

/-- The bound variable occurs positively, so the generator is a fixed point and
not merely a lower bound. -/
theorem reachableBody_positiveIn (atom : String) :
    OSLFFormula.positiveIn 0 (reachableBody atom) = true := rfl

/-- The fixed point law, instantiated: the generator denotes what its own
unfolding denotes. -/
theorem sem_reachable_eq_unfold (R : Pattern → Pattern → Prop) (I : AtomSem)
    (atom : String) :
    sem R I (reachable atom) = sem R I (OSLFFormula.unfold (reachableBody atom)) :=
  sem_mu_eq_unfold R I (reachableBody atom)
    (reachableBody_closedAt atom) (reachableBody_positiveIn atom)

/-- **The extension.**  The five symbols describe exactly the terms from which
an observed term is reachable.  This is an equality, not a bound: the left side
is the intersection over every pre-fixed point and the right side is a concrete
region, and they coincide. -/
theorem sem_reachable_iff (R : Pattern → Pattern → Prop) (I : AtomSem)
    (atom : String) (p : Pattern) :
    sem R I (reachable atom) p ↔ ∃ q, Relation.ReflTransGen R p q ∧ I atom q := by
  constructor
  · intro holds
    refine holds (fun t => ∃ q, Relation.ReflTransGen R t q ∧ I atom q) trivial ?_
    intro t ht
    rcases ht with observed | ⟨u, step, q, path, observed⟩
    · exact ⟨t, Relation.ReflTransGen.refl, observed⟩
    · exact ⟨q, Relation.ReflTransGen.head step path, observed⟩
  · rintro ⟨q, path, observed⟩ candidate _ pre
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact pre q (Or.inl observed)
    | head step _ inner => exact pre _ (Or.inr ⟨_, step, inner⟩)

/-! ## A system in which that region is infinite

The description does not grow with the region.  Here is a system where the
region is unbounded and the formula that generates it is the same five symbols
at every depth. -/

/-- The observed state. -/
def base : Pattern := .fvar "z"

/-- One step away from its argument. -/
def succ (p : Pattern) : Pattern := .apply "s" [p]

/-- `succ` iterated. -/
def chain : Nat → Pattern
  | 0 => base
  | n + 1 => succ (chain n)

/-- The executable step: a successor term steps to its argument. -/
def stepFn : Pattern → List Pattern
  | .apply "s" [q] => [q]
  | _ => []

/-- The executable observation: only the base is observed. -/
def atomFn : AtomCheck := fun a p => a == "a" && p == base

/-- The semantic observation the checker reflects. -/
def atomSem : AtomSem := fun a p => a = "a" ∧ p = base

theorem atomFn_sound : ∀ a p, atomFn a p = true → atomSem a p := by
  intro a p h
  simp only [atomFn, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

/-- Every term of the chain steps to its predecessor. -/
theorem stepFn_chain (n : Nat) : chain n ∈ stepFn (chain (n + 1)) := by
  simp [chain, succ, stepFn]

/-- The relation the checker's step function underapproximates. -/
def stepRel (p q : Pattern) : Prop := q ∈ stepFn p

/-- Every term of the chain reaches the base. -/
theorem chain_reaches (n : Nat) : Relation.ReflTransGen stepRel (chain n) base := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
      exact Relation.ReflTransGen.head (by exact stepFn_chain k) ih

/-- **One generator, an infinite region.**  The same five-symbol formula holds
at every term of the chain, at every depth. -/
theorem sem_reachable_chain (n : Nat) :
    sem stepRel atomSem (reachable "a") (chain n) :=
  (sem_reachable_iff stepRel atomSem "a" (chain n)).mpr
    ⟨base, chain_reaches n, rfl, rfl⟩

/-- And it fails where nothing is reachable. -/
theorem sem_reachable_isolated :
    ¬ sem stepRel atomSem (reachable "a") (.fvar "w") := by
  intro holds
  obtain ⟨q, path, observed⟩ := (sem_reachable_iff stepRel atomSem "a" (.fvar "w")).mp holds
  rcases Relation.ReflTransGen.cases_head path with rfl | ⟨u, step, _⟩
  · exact absurd observed.2 (by simp [base])
  · exact absurd step (by simp [stepRel, stepFn])

/-! ## The checker reaches it

The generator is decided by descent: one unfolding per unit of fuel.  The two
computations below are kernel-checked, so they are the executable side of the
same statement, not a separate claim about it. -/

theorem check_reachable_chain_three :
    check stepFn atomFn 40 (chain 3) (reachable "a") = .sat := by
  decide +kernel

theorem check_reachable_isolated :
    check stepFn atomFn 40 (.fvar "w") (reachable "a") = .unsat := by
  decide +kernel

/-- The description is fixed and the search is not: with the fuel cut to what a
shallower term needs, the same query on a deeper term is answered `unknown`
rather than wrongly. -/
theorem check_reachable_starved :
    check stepFn atomFn 6 (chain 3) (reachable "a") = .unknown := by
  decide +kernel

/-- What the checker finds, the semantics has. -/
theorem check_sat_gives_sem :
    sem stepRel atomSem (reachable "a") (chain 3) :=
  check_sat_sound atomFn_sound (fun _ _ h => h) check_reachable_chain_three

/-! ## The counting law

The source material's stratum count: the first stratum has two members, and
each next stratum has two more than the number of unordered pairs it can draw
from the previous one together with a fresh member.  The description of a
stratum grows by a constant; the stratum squares. -/

/-- `u₀ = 2`, `u_{j+1} = 2 + (u_j + 1) * u_j / 2`. -/
def stratum : Nat → Nat
  | 0 => 2
  | n + 1 => 2 + (stratum n + 1) * stratum n / 2

/-- The closed form is the binomial coefficient the source writes. -/
theorem stratum_succ_eq_choose (n : Nat) :
    stratum (n + 1) = 2 + Nat.choose (stratum n + 1) 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  simp only [stratum]

/-- The first six strata, kernel-checked. -/
theorem stratum_values :
    (List.range 6).map stratum = [2, 5, 17, 155, 12092, 73114280] := by
  decide +kernel

/-- The counting law is superlinear: each stratum is at least the previous one
squared and halved.  That is the half of the contrast the arithmetic carries;
the other half is `reachable_size`, where the description does not grow at
all. -/
theorem stratum_superlinear (n : Nat) :
    stratum n * stratum n / 2 ≤ stratum (n + 1) :=
  calc stratum n * stratum n / 2 ≤ (stratum n + 1) * stratum n / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ _))
    _ ≤ 2 + (stratum n + 1) * stratum n / 2 := Nat.le_add_left _ _
    _ = stratum (n + 1) := rfl

end Mettapedia.OSLF.Framework.GeneratorLength
