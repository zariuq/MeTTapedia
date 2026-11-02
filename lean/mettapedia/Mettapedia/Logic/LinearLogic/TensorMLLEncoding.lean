import Mettapedia.Logic.LinearLogic.TensorSequent
import Mettapedia.GSLT.Logic.PropositionalMLLBalance

/-!
# Tensor transition proofs compile into the existing closed MLL calculus

An actual tensor-sequent proof supplies one linear implication hypothesis
per transition use. Its MLL translation contains the duals of the original
linear hypotheses, the positive conclusion, and exactly that finite multiset
of declaration copies. Repeated use of a persistent declaration creates
different linear copies; initial resource hypotheses are never contracted.

The target is the existing `PropositionalMLL.Derives`, through its exchange-
only multiset presentation. This is a proof-preserving forward translation. Arbitrary
MLL proof reflection and the full exponential formula syntax are separate.
Generic faithful reflection must exclude collisions in the atom encoding.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.TensorMLLEncoding

open Mettapedia.GSLT.Logic

universe uAtom uRule
variable {Atom : Type uAtom} {Rule : Type uRule}

def encode (code : Atom → Nat) : TensorSequent.Formula Atom → PropositionalMLL.Formula
  | .atom name => .atom (code name)
  | .one => .one
  | .tensor left right => .tensor (encode code left) (encode code right)

theorem encode_injective (code : Atom → Nat) (injective : Function.Injective code) :
    Function.Injective (encode code) := by
  intro first
  induction first with
  | atom name =>
      intro second same
      cases second with
      | atom other => exact congrArg TensorSequent.Formula.atom (injective (PropositionalMLL.Formula.atom.inj same))
      | one => cases same
      | tensor left right => cases same
  | one =>
      intro second same
      cases second with
      | atom name => cases same
      | one => rfl
      | tensor left right => cases same
  | tensor left right ihLeft ihRight =>
      intro second same
      cases second with
      | atom name => cases same
      | one => cases same
      | tensor otherLeft otherRight =>
          have parts := PropositionalMLL.Formula.tensor.inj same
          exact congrArg₂ TensorSequent.Formula.tensor (ihLeft parts.1) (ihRight parts.2)

def negativeContext (code : Atom → Nat) (context : Multiset (TensorSequent.Formula Atom)) :
    Multiset PropositionalMLL.Formula := context.map (fun formula => PropositionalMLL.dual (encode code formula))

def negativeAtoms (code : Atom → Nat) (atoms : Multiset Atom) : Multiset PropositionalMLL.Formula :=
  atoms.map (fun name => PropositionalMLL.Formula.natom (code name))

@[simp] theorem negativeContext_add (code : Atom → Nat) (first second : Multiset (TensorSequent.Formula Atom)) :
    negativeContext code (first + second) = negativeContext code first + negativeContext code second :=
  Multiset.map_add _ _ _

@[simp] theorem negativeContext_cons (code : Atom → Nat) (formula : TensorSequent.Formula Atom)
    (context : Multiset (TensorSequent.Formula Atom)) :
    negativeContext code (formula ::ₘ context) =
      PropositionalMLL.dual (encode code formula) ::ₘ negativeContext code context := by simp [negativeContext]

@[simp] theorem negative_atom_context (code : Atom → Nat) (atoms : Multiset Atom) :
    negativeContext code (TensorSequent.atomContext atoms) = negativeAtoms code atoms := by
  simp only [negativeContext, TensorSequent.atomContext, Multiset.map_map, negativeAtoms]
  rfl

noncomputable def ruleFormula (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom) (rule : Rule) :
    PropositionalMLL.Formula :=
  .par (PropositionalMLL.dual (encode code (TensorSequent.Formula.ofMultiset (premises rule))))
    (encode code (TensorSequent.Formula.ofMultiset (conclusions rule)))

@[simp] theorem dual_ruleFormula (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom) (rule : Rule) :
    PropositionalMLL.dual (ruleFormula code premises conclusions rule) =
      .tensor (encode code (TensorSequent.Formula.ofMultiset (premises rule)))
        (PropositionalMLL.dual (encode code (TensorSequent.Formula.ofMultiset (conclusions rule)))) := by
  simp only [ruleFormula, PropositionalMLL.dual, PropositionalMLL.dual_involutive]

noncomputable def ruleCopies (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom) (uses : List Rule) :
    Multiset PropositionalMLL.Formula :=
  (uses.map fun rule => PropositionalMLL.dual (ruleFormula code premises conclusions rule) : List PropositionalMLL.Formula)

@[simp] theorem ruleCopies_nil (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom) :
    ruleCopies code premises conclusions [] = 0 := rfl

@[simp] theorem ruleCopies_cons (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom)
    (rule : Rule) (uses : List Rule) :
    ruleCopies code premises conclusions (rule :: uses) =
      PropositionalMLL.dual (ruleFormula code premises conclusions rule) ::ₘ ruleCopies code premises conclusions uses := rfl

@[simp] theorem ruleCopies_append (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom)
    (first second : List Rule) :
    ruleCopies code premises conclusions (first ++ second) =
      ruleCopies code premises conclusions first + ruleCopies code premises conclusions second := by
  simp only [ruleCopies, List.map_append, ← Multiset.coe_add]

theorem assemble (code : Atom → Nat) : ∀ formula : TensorSequent.Formula Atom,
    PropositionalMLL.Bag.Provable (encode code formula ::ₘ negativeAtoms code formula.atoms)
  | .atom name => PropositionalMLL.Bag.atom (code name)
  | .one => PropositionalMLL.Bag.one
  | .tensor left right => by
      apply PropositionalMLL.Bag.cast _ (PropositionalMLL.Bag.tensor (assemble code left) (assemble code right))
      simp [encode, TensorSequent.Formula.atoms, negativeAtoms]

/-- The copied implication is consumed once by the existing MLL tensor
rule; it is not installed as a new axiom of that target calculus. -/
theorem transition (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom) (rule : Rule) :
    PropositionalMLL.Bag.Provable
      (encode code (TensorSequent.Formula.ofMultiset (conclusions rule)) ::ₘ
        (negativeContext code (TensorSequent.atomContext (premises rule)) + ruleCopies code premises conclusions [rule])) := by
  have input : PropositionalMLL.Bag.Provable
      (encode code (TensorSequent.Formula.ofMultiset (premises rule)) ::ₘ
        negativeContext code (TensorSequent.atomContext (premises rule))) :=
    PropositionalMLL.Bag.cast (by simp) (assemble code (TensorSequent.Formula.ofMultiset (premises rule)))
  have output : PropositionalMLL.Bag.Provable
      (PropositionalMLL.dual (encode code (TensorSequent.Formula.ofMultiset (conclusions rule))) ::ₘ
        {encode code (TensorSequent.Formula.ofMultiset (conclusions rule))}) :=
    PropositionalMLL.Bag.cast (by simp [PropositionalMLL.dual_involutive])
      (PropositionalMLL.Bag.identity (PropositionalMLL.dual (encode code (TensorSequent.Formula.ofMultiset (conclusions rule)))))
  apply PropositionalMLL.Bag.cast _ (PropositionalMLL.Bag.tensor input output)
  simp only [ruleCopies_cons, ruleCopies_nil, dual_ruleFormula, ← Multiset.singleton_add, add_zero]
  ac_rfl

/-- Every rule-use occurrence yields exactly one copied implication in an
actual existing MLL proof. Polarity and the original linear hypotheses are
retained separately from the declaration copies. -/
theorem compile (code : Atom → Nat) {premises conclusions : Rule → Multiset Atom}
    {context : Multiset (TensorSequent.Formula Atom)} {goal : TensorSequent.Formula Atom}
    (proof : TensorSequent.Derives premises conclusions context goal) :
    PropositionalMLL.Bag.Provable
      (encode code goal ::ₘ (negativeContext code context + ruleCopies code premises conclusions proof.uses)) := by
  induction proof with
  | atomId name => exact PropositionalMLL.Bag.atom (code name)
  | transition rule => exact transition code premises conclusions rule
  | oneR => exact PropositionalMLL.Bag.one
  | @oneL context goal prior ih =>
      apply PropositionalMLL.Bag.cast _ (PropositionalMLL.Bag.bot ih)
      simp only [negativeContext_cons, encode, PropositionalMLL.dual, TensorSequent.Derives.uses]
      simp only [← Multiset.singleton_add]
      ac_rfl
  | @tensorR leftContext rightContext left right first second ihFirst ihSecond =>
      apply PropositionalMLL.Bag.cast _ (PropositionalMLL.Bag.tensor ihFirst ihSecond)
      simp only [encode, negativeContext_add, TensorSequent.Derives.uses, ruleCopies_append]
      simp only [← Multiset.singleton_add]
      ac_rfl
  | @tensorL context left right goal prior ih =>
      have exposed : PropositionalMLL.Bag.Provable
          (PropositionalMLL.dual (encode code left) ::ₘ PropositionalMLL.dual (encode code right) ::ₘ
            (encode code goal ::ₘ (negativeContext code context + ruleCopies code premises conclusions prior.uses))) :=
        PropositionalMLL.Bag.cast (by simp only [negativeContext_cons]; simp only [← Multiset.singleton_add]; ac_rfl) ih
      apply PropositionalMLL.Bag.cast _ (PropositionalMLL.Bag.par exposed)
      simp only [negativeContext_cons, encode, PropositionalMLL.dual, TensorSequent.Derives.uses]
      simp only [← Multiset.singleton_add]
      ac_rfl
  | @cut leftContext rightContext cutFormula goal first second ihFirst ihSecond =>
      have exposed : PropositionalMLL.Bag.Provable
          (PropositionalMLL.dual (encode code cutFormula) ::ₘ
            (encode code goal ::ₘ (negativeContext code rightContext + ruleCopies code premises conclusions second.uses))) :=
        PropositionalMLL.Bag.cast (by simp only [negativeContext_cons]; simp only [← Multiset.singleton_add]; ac_rfl) ihSecond
      apply PropositionalMLL.Bag.cast _ (PropositionalMLL.Bag.cut ihFirst exposed)
      simp only [negativeContext_add, TensorSequent.Derives.uses, ruleCopies_append]
      simp only [← Multiset.singleton_add]
      ac_rfl

theorem charge_encode (code : Atom → Nat) (weight : Nat → Int) (formula : TensorSequent.Formula Atom) :
    PropositionalMLL.Balance.charge weight (encode code formula) =
      (formula.atoms.map fun name => weight (code name)).sum := by
  induction formula with
  | atom name => simp [encode, PropositionalMLL.Balance.charge, TensorSequent.Formula.atoms]
  | one => rfl
  | tensor left right ihLeft ihRight =>
      simp only [encode, PropositionalMLL.Balance.charge, TensorSequent.Formula.atoms,
        Multiset.map_add, Multiset.sum_add, ihLeft, ihRight]

theorem charge_ruleCopy (code : Atom → Nat) (weight : Nat → Int)
    (premises conclusions : Rule → Multiset Atom) (rule : Rule) :
    PropositionalMLL.Balance.charge weight (PropositionalMLL.dual (ruleFormula code premises conclusions rule)) =
      (premises rule |>.map fun name => weight (code name)).sum -
        (conclusions rule |>.map fun name => weight (code name)).sum := by
  simp only [dual_ruleFormula, PropositionalMLL.Balance.charge, PropositionalMLL.Balance.charge_dual,
    charge_encode, TensorSequent.Formula.atoms_ofMultiset, sub_eq_add_neg]

theorem ruleCopies_card (code : Atom → Nat) (premises conclusions : Rule → Multiset Atom) (uses : List Rule) :
    (ruleCopies code premises conclusions uses).card = uses.length := by simp [ruleCopies]

theorem balanced_ruleCopies (code : Atom → Nat) (weight : Nat → Int)
    (premises conclusions : Rule → Multiset Atom)
    (balanced : ∀ rule, (premises rule |>.map fun name => weight (code name)).sum =
      (conclusions rule |>.map fun name => weight (code name)).sum) (uses : List Rule) :
    PropositionalMLL.Balance.bagTotal weight (ruleCopies code premises conclusions uses) = 0 := by
  induction uses with
  | nil => rfl
  | cons rule uses ih =>
      change PropositionalMLL.Balance.charge weight (PropositionalMLL.dual (ruleFormula code premises conclusions rule)) +
        PropositionalMLL.Balance.bagTotal weight (ruleCopies code premises conclusions uses) = 0
      rw [charge_ruleCopy, balanced, sub_self, ih, add_zero]

end Mettapedia.Logic.LinearLogic.TensorMLLEncoding
