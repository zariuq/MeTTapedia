import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic

/-!
# Tensor sequents with declared transition rules

The positive multiplicative fragment has atoms, tensor and its unit. This is
a two-sided sequent calculus with atom identity, tensor left/right, unit
left/right, cut, and external transition declarations. Antecedents are
multisets, so exchange is structural. There is no weakening or contraction
of antecedent resources. The declared rule family is reusable, with a
separate proof leaf for every actual use.

Conclusions retain all resources. A planning goal which tolerates leftovers
must explicitly quantify a residual tensor; the tensor unit is an exact
empty boundary and does not discard resources. No transition, execution or
reachability relation is used to define these logical proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.TensorSequent

universe uAtom uRule

inductive Formula (Atom : Type uAtom) where
  | atom (name : Atom)
  | one
  | tensor (left right : Formula Atom)

namespace Formula

variable {Atom : Type uAtom}

def atoms : Formula Atom → Multiset Atom
  | .atom name => {name}
  | .one => 0
  | .tensor left right => left.atoms + right.atoms

def ofList : List Atom → Formula Atom
  | [] => .one
  | name :: rest => .tensor (.atom name) (ofList rest)

@[simp] theorem atoms_ofList (names : List Atom) : (ofList names).atoms = (names : Multiset Atom) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp only [ofList, atoms, ih, Multiset.singleton_add]
      rfl

/-- A chosen parenthesization of a multiset. Proofs below are independent of
that choice; exchange and the tensor/unit rules compare other presentations. -/
noncomputable def ofMultiset (names : Multiset Atom) : Formula Atom := ofList names.toList

@[simp] theorem atoms_ofMultiset (names : Multiset Atom) : (ofMultiset names).atoms = names := by
  simp only [ofMultiset, atoms_ofList, Multiset.coe_toList]

end Formula

variable {Atom : Type uAtom}

def contextAtoms (context : Multiset (Formula Atom)) : Multiset Atom := context.bind Formula.atoms

def atomContext (names : Multiset Atom) : Multiset (Formula Atom) := names.map Formula.atom

@[simp] theorem atomContext_cons (name : Atom) (names : Multiset Atom) :
    atomContext (name ::ₘ names) = Formula.atom name ::ₘ atomContext names := by simp [atomContext]

@[simp] theorem contextAtoms_zero : contextAtoms (0 : Multiset (Formula Atom)) = 0 := rfl
@[simp] theorem contextAtoms_cons (formula : Formula Atom) (context : Multiset (Formula Atom)) :
    contextAtoms (formula ::ₘ context) = formula.atoms + contextAtoms context :=
  Multiset.cons_bind _ _ _
@[simp] theorem contextAtoms_add (first second : Multiset (Formula Atom)) :
    contextAtoms (first + second) = contextAtoms first + contextAtoms second :=
  Multiset.add_bind _ _ _
@[simp] theorem contextAtoms_atomContext (names : Multiset Atom) : contextAtoms (atomContext names) = names := by
  induction names using Multiset.induction_on with
  | empty => rfl
  | @cons name names ih =>
      rw [atomContext_cons]
      rw [contextAtoms_cons, show (Formula.atom name).atoms = ({name} : Multiset Atom) from rfl, ih]
      rfl

inductive Derives {Rule : Type uRule} (premises conclusions : Rule → Multiset Atom) :
    Multiset (Formula Atom) → Formula Atom → Type (max uAtom uRule) where
  | atomId (name : Atom) : Derives premises conclusions {Formula.atom name} (.atom name)
  | transition (rule : Rule) :
      Derives premises conclusions (atomContext (premises rule)) (Formula.ofMultiset (conclusions rule))
  | oneR : Derives premises conclusions 0 .one
  | oneL {context goal} : Derives premises conclusions context goal →
      Derives premises conclusions (Formula.one ::ₘ context) goal
  | tensorR {leftContext rightContext left right} :
      Derives premises conclusions leftContext left → Derives premises conclusions rightContext right →
        Derives premises conclusions (leftContext + rightContext) (.tensor left right)
  | tensorL {context left right goal} :
      Derives premises conclusions (left ::ₘ right ::ₘ context) goal →
        Derives premises conclusions (Formula.tensor left right ::ₘ context) goal
  | cut {leftContext rightContext cutFormula goal} :
      Derives premises conclusions leftContext cutFormula →
      Derives premises conclusions (cutFormula ::ₘ rightContext) goal →
        Derives premises conclusions (leftContext + rightContext) goal

namespace Derives

variable {Rule : Type uRule} {premises conclusions : Rule → Multiset Atom}

/-- Program declarations may recur as different leaves. Tensor and cut use
the displayed left-then-right readout; they do not identify other orders. -/
def uses : {context : Multiset (Formula Atom)} → {goal : Formula Atom} →
    Derives premises conclusions context goal → List Rule
  | _, _, .atomId _ => []
  | _, _, .transition rule => [rule]
  | _, _, .oneR => []
  | _, _, .oneL proof => proof.uses
  | _, _, .tensorR first second => first.uses ++ second.uses
  | _, _, .tensorL proof => proof.uses
  | _, _, .cut first second => first.uses ++ second.uses

def identity : (formula : Formula Atom) → Derives premises conclusions {formula} formula
  | .atom name => .atomId name
  | .one => .oneL .oneR
  | .tensor left right => .tensorL (.tensorR (identity left) (identity right))

@[simp] theorem uses_identity (formula : Formula Atom) :
    (identity (premises := premises) (conclusions := conclusions) formula).uses = [] := by
  induction formula with
  | atom => rfl
  | one => rfl
  | tensor left right ihLeft ihRight => simp [identity, uses, ihLeft, ihRight]

end Derives

end Mettapedia.Logic.LinearLogic.TensorSequent
