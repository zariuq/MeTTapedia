import Mettapedia.GSLT.Logic.PropositionalMLLBag
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
# Signed atom weights are conserved by every existing MLL proof

Atoms receive arbitrary integer weights, dual atoms their negatives, and
both multiplicatives add weights. Every derivable one-sided sequent has
total weight zero, including proofs with arbitrary formula cuts. This is an
independent algebraic necessary condition, not a proof-search invariant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalMLL.Balance

def charge (weight : Nat → Int) : Formula → Int
  | .atom name => weight name
  | .natom name => - weight name
  | .one => 0
  | .bot => 0
  | .tensor left right => charge weight left + charge weight right
  | .par left right => charge weight left + charge weight right

@[simp] theorem charge_dual (weight : Nat → Int) (formula : Formula) :
    charge weight (dual formula) = - charge weight formula := by
  induction formula with
  | atom => rfl
  | natom => simp [charge, dual]
  | one => rfl
  | bot => rfl
  | tensor left right ihLeft ihRight => simp [charge, dual, ihLeft, ihRight, add_comm]
  | par left right ihLeft ihRight => simp [charge, dual, ihLeft, ihRight, add_comm]

def total (weight : Nat → Int) (context : List Formula) : Int := (context.map (charge weight)).sum

@[simp] theorem total_cons (weight : Nat → Int) (head : Formula) (tail : List Formula) :
    total weight (head :: tail) = charge weight head + total weight tail := rfl

@[simp] theorem total_append (weight : Nat → Int) (first second : List Formula) :
    total weight (first ++ second) = total weight first + total weight second := by simp [total]

theorem conserved (weight : Nat → Int) {context : List Formula} (proof : Derives context) : total weight context = 0 := by
  induction proof with
  | ax name => simp [total, charge]
  | one => rfl
  | bot prior ih => simpa only [total_cons, charge, zero_add] using ih
  | tensor first second ihFirst ihSecond =>
      simp only [total_cons, total_append, charge] at *
      omega
  | par prior ih =>
      simp only [total_cons, charge] at *
      omega
  | cut first second ihFirst ihSecond =>
      simp only [total_cons, charge_dual, total_append] at *
      omega
  | ex prior perm ih =>
      have same := (perm.map (charge weight)).sum_eq
      exact same.symm.trans ih

def bagTotal (weight : Nat → Int) (context : Multiset Formula) : Int := (context.map (charge weight)).sum

@[simp] theorem bagTotal_cons (weight : Nat → Int) (head : Formula) (tail : Multiset Formula) :
    bagTotal weight (head ::ₘ tail) = charge weight head + bagTotal weight tail := by simp [bagTotal]

@[simp] theorem bagTotal_add (weight : Nat → Int) (first second : Multiset Formula) :
    bagTotal weight (first + second) = bagTotal weight first + bagTotal weight second := by simp [bagTotal]

@[simp] theorem bagTotal_list (weight : Nat → Int) (context : List Formula) :
    bagTotal weight (context : Multiset Formula) = total weight context := rfl

theorem bag_conserved (weight : Nat → Int) {context : Multiset Formula} (proof : Bag.Provable context) :
    bagTotal weight context = 0 := by
  obtain ⟨ordered, presentation, ⟨actual⟩⟩ := proof
  rw [← presentation, bagTotal_list]
  exact conserved weight actual

end Mettapedia.GSLT.Logic.PropositionalMLL.Balance
