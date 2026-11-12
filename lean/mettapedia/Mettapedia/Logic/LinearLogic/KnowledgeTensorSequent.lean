import Mettapedia.Logic.LinearLogic.KnowledgeTensorLending

/-!
# A sequent calculus with tensor and unit over the three zones

Formulas are atoms, the unit and tensor. A sequent has a knowledge zone, a lent zone of atoms, a
multiset of owned formulas on the left and one formula on the right, and its conclusion states
the knowledge reached. The rules are atom identity, one leaf per use of a declaration, the left
and right rules of unit and tensor, cut on an arbitrary formula, and the three zone rules: `grow`
lends more, `lend` turns owned atoms into lent ones for a sub-proof, `strengthen` adds knowledge.
Tensor on the right composes two proofs from the same knowledge and joins what they learn. There
is no weakening and no contraction of owned formulas.

## Results

* `Sequent.lends`: a sequent proof is a proof of the three-zone calculus between the atoms of its
  two sides, with the same leaves.
* `Lends.sequent`: a proof of the three-zone calculus is a sequent proof from its atoms to the
  tensor of its atoms.
* `sequent_iff_runUnder`: at atomic boundaries, sequent proofs are exactly the runs under the
  lent context.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

namespace System

open TensorSequent

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]

/-- Sequent proofs over the three zones. The list is the left-to-right readout of the leaves. -/
inductive Sequent (system : System K Atom Rule) :
    Multiset Atom → K → Multiset (Formula Atom) → List Rule → K → Formula Atom → Prop
  | atomId (lent : Multiset Atom) (k : K) (name : Atom) :
      Sequent system lent k {Formula.atom name} [] k (Formula.atom name)
  | transition (declaration : Rule) (k : K)
      (asked : system.guard declaration (k ⊓ system.tell declaration)) :
      Sequent system (system.read declaration) k (atomContext (system.take declaration))
        [declaration] (k ⊓ system.tell declaration) (Formula.ofMultiset (system.make declaration))
  | oneR (lent : Multiset Atom) (k : K) : Sequent system lent k 0 [] k Formula.one
  | oneL {lent : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)} {uses : List Rule}
      {goal : Formula Atom} :
      Sequent system lent k context uses k' goal →
        Sequent system lent k (Formula.one ::ₘ context) uses k' goal
  | tensorR {lent : Multiset Atom} {k k₁ k₂ : K} {leftContext rightContext : Multiset (Formula Atom)}
      {first second : List Rule} {left right : Formula Atom} :
      Sequent system lent k leftContext first k₁ left →
      Sequent system lent k rightContext second k₂ right →
        Sequent system lent k (leftContext + rightContext) (first ++ second) (k₁ ⊓ k₂)
          (Formula.tensor left right)
  | tensorL {lent : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)} {uses : List Rule}
      {left right goal : Formula Atom} :
      Sequent system lent k (left ::ₘ right ::ₘ context) uses k' goal →
        Sequent system lent k (Formula.tensor left right ::ₘ context) uses k' goal
  | cut {lent : Multiset Atom} {k k₁ k' : K} {leftContext rightContext : Multiset (Formula Atom)}
      {first second : List Rule} {cutFormula goal : Formula Atom} :
      Sequent system lent k leftContext first k₁ cutFormula →
      Sequent system lent k₁ (cutFormula ::ₘ rightContext) second k' goal →
        Sequent system lent k (leftContext + rightContext) (first ++ second) k' goal
  | grow {lent wider : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)}
      {uses : List Rule} {goal : Formula Atom} (within : lent ≤ wider) :
      Sequent system lent k context uses k' goal → Sequent system wider k context uses k' goal
  | lend {lent : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)} {uses : List Rule}
      {goal : Formula Atom} (borrowed : Multiset Atom) :
      Sequent system (lent + borrowed) k context uses k' goal →
        Sequent system lent k (context + atomContext borrowed) uses k'
          (Formula.tensor goal (Formula.ofMultiset borrowed))
  | strengthen {lent : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)}
      {uses : List Rule} {goal : Formula Atom} (more : K) :
      Sequent system lent k context uses k' goal →
        Sequent system lent (k ⊓ more) context uses (k' ⊓ more) goal

variable {sys : System K Atom Rule}

/-! ## From sequents to the three-zone calculus -/

/-- A sequent proof is a three-zone proof between the atoms of its two sides. -/
theorem Sequent.lends {lent : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)}
    {uses : List Rule} {goal : Formula Atom} (proof : Sequent sys lent k context uses k' goal) :
    sys.Lends lent k (contextAtoms context) uses k' goal.atoms := by
  induction proof with
  | atomId lent k name => exact Lends.identity lent k {name}
  | transition declaration k asked =>
      rw [TensorSequent.contextAtoms_atomContext, TensorSequent.Formula.atoms_ofMultiset]
      exact Lends.rule declaration k asked
  | oneR lent k => exact Lends.identity lent k 0
  | @oneL lent k k' context uses goal prior ih =>
      have same : contextAtoms (Formula.one ::ₘ context) = contextAtoms context := by
        simp [Formula.atoms]
      rw [same]
      exact ih
  | tensorR first second ihFirst ihSecond =>
      rw [TensorSequent.contextAtoms_add]
      exact Lends.tensor ihFirst ihSecond
  | @tensorL lent k k' context uses left right goal prior ih =>
      have same : contextAtoms (left ::ₘ right ::ₘ context) =
          contextAtoms (Formula.tensor left right ::ₘ context) := by
        simp [Formula.atoms, add_assoc]
      rw [← same]
      exact ih
  | @cut lent k k₁ k' leftContext rightContext first second cutFormula goal one two ihFirst ihSecond =>
      rw [TensorSequent.contextAtoms_add]
      rw [TensorSequent.contextAtoms_cons] at ihSecond
      exact Lends.cut (Lends.frame (contextAtoms rightContext) ihFirst) ihSecond
  | grow within prior ih => exact Lends.grow within ih
  | @lend lent k k' context uses goal borrowed prior ih =>
      have target : (Formula.tensor goal (Formula.ofMultiset borrowed)).atoms =
          goal.atoms + borrowed := by
        simp [Formula.atoms]
      rw [TensorSequent.contextAtoms_add, TensorSequent.contextAtoms_atomContext, target]
      exact Lends.lend borrowed ih
  | strengthen more prior ih => exact Lends.strengthen more ih

/-! ## Structural sequent proofs -/

/-- Every formula is proved from its atoms, with no leaf. -/
theorem Sequent.fromAtoms (lent : Multiset Atom) (k : K) (goal : Formula Atom) :
    Sequent sys lent k (atomContext goal.atoms) [] k goal := by
  induction goal with
  | atom name => exact Sequent.atomId lent k name
  | one => exact Sequent.oneR lent k
  | tensor left right ihLeft ihRight =>
      have both := Sequent.tensorR ihLeft ihRight
      have source : atomContext left.atoms + atomContext right.atoms =
          atomContext (Formula.tensor left right).atoms := (TensorSequent.atomContext_add _ _).symm
      rw [inf_idem, source] at both
      exact both

/-- The atoms of a formula on the left may be packed into that formula. -/
theorem Sequent.condense {lent : Multiset Atom} {uses : List Rule} {goal : Formula Atom}
    (formula : Formula Atom) :
    ∀ (context : Multiset (Formula Atom)) {k k' : K},
      Sequent sys lent k (atomContext formula.atoms + context) uses k' goal →
        Sequent sys lent k (formula ::ₘ context) uses k' goal := by
  induction formula with
  | atom name =>
      intro context k k' proof
      exact proof
  | one =>
      intro context k k' proof
      have same : atomContext (Formula.one (Atom := Atom)).atoms + context = context := by
        simp [atomContext, Formula.atoms]
      rw [same] at proof
      exact Sequent.oneL proof
  | tensor left right ihLeft ihRight =>
      intro context k k' proof
      have firstContext : atomContext (Formula.tensor left right).atoms + context =
          atomContext left.atoms + (atomContext right.atoms + context) := by
        simp only [Formula.atoms, TensorSequent.atomContext_add, add_assoc]
      rw [firstContext] at proof
      have first := ihLeft (atomContext right.atoms + context) proof
      have secondContext : left ::ₘ (atomContext right.atoms + context) =
          atomContext right.atoms + (left ::ₘ context) := by
        simp only [← Multiset.singleton_add]
        ac_rfl
      rw [secondContext] at first
      have second := ihRight (left ::ₘ context) first
      rw [Multiset.cons_swap] at second
      exact Sequent.tensorL second

/-- The goal may be repackaged into any formula with the same atoms. -/
theorem Sequent.repackage {lent : Multiset Atom} {k k' : K} {context : Multiset (Formula Atom)}
    {uses : List Rule} {left right : Formula Atom}
    (proof : Sequent sys lent k context uses k' left) (same : left.atoms = right.atoms) :
    Sequent sys lent k context uses k' right := by
  have raw := Sequent.fromAtoms (sys := sys) lent k' right
  rw [← same] at raw
  have opened : Sequent sys lent k' (atomContext left.atoms + 0) [] k' right := by
    rw [add_zero]
    exact raw
  have joined := Sequent.cut proof (Sequent.condense left 0 opened)
  rw [add_zero, List.append_nil] at joined
  exact joined

/-! ## From the three-zone calculus to sequents -/

/-- A three-zone proof is a sequent proof from its atoms to the tensor of its atoms. -/
theorem Lends.sequent {lent : Multiset Atom} {k k' : K} {Γ Γ' : Multiset Atom} {uses : List Rule}
    (proof : sys.Lends lent k Γ uses k' Γ') :
    Sequent sys lent k (atomContext Γ) uses k' (Formula.ofMultiset Γ') := by
  induction proof with
  | identity lent k Γ =>
      have raw := Sequent.fromAtoms (sys := sys) lent k (Formula.ofMultiset Γ)
      rw [TensorSequent.Formula.atoms_ofMultiset] at raw
      exact raw
  | rule declaration k asked => exact Sequent.transition declaration k asked
  | grow within prior ih => exact Sequent.grow within ih
  | @lend lent k k' Γ Γ' uses borrowed prior ih =>
      have returned := Sequent.lend borrowed ih
      rw [← TensorSequent.atomContext_add] at returned
      exact Sequent.repackage returned (by simp [Formula.atoms])
  | strengthen more prior ih => exact Sequent.strengthen more ih
  | @cut lent k k₁ k' Γ Γ₁ Γ' first second one two ihFirst ihSecond =>
      have opened : Sequent sys lent k₁ (atomContext (Formula.ofMultiset Γ₁).atoms + 0) second k'
          (Formula.ofMultiset Γ') := by
        rw [TensorSequent.Formula.atoms_ofMultiset, add_zero]
        exact ihSecond
      have joined := Sequent.cut ihFirst (Sequent.condense (Formula.ofMultiset Γ₁) 0 opened)
      rw [add_zero] at joined
      exact joined

/-- **At atomic boundaries, sequent proofs are exactly the runs under the lent context**, with
the same leaves in the same order. -/
theorem sequent_iff_runUnder (lent : Multiset Atom) (k k' : K) (Γ Γ' : Multiset Atom)
    (uses : List Rule) :
    Sequent sys lent k (atomContext Γ) uses k' (Formula.ofMultiset Γ') ↔
      sys.RunUnder lent k Γ uses k' Γ' := by
  constructor
  · intro proof
    have lends := Sequent.lends proof
    rw [TensorSequent.contextAtoms_atomContext, TensorSequent.Formula.atoms_ofMultiset] at lends
    exact Lends.run lends
  · intro run
    exact Lends.sequent (RunUnder.lends run)

/-- With nothing lent, sequent proofs at atomic boundaries are exactly the runs. -/
theorem sequent_iff_run (k k' : K) (Γ Γ' : Multiset Atom) (uses : List Rule) :
    Sequent sys 0 k (atomContext Γ) uses k' (Formula.ofMultiset Γ') ↔ sys.Run k Γ uses k' Γ' :=
  (sequent_iff_runUnder 0 k k' Γ Γ' uses).trans (runUnder_zero_iff_run k k' Γ Γ' uses)

end System

end Mettapedia.Logic.LinearLogic.KnowledgeTensor
