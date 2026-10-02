import Mettapedia.GSLT.Logic.QuotientObservers
import Mettapedia.GSLT.Scope.ConsumerDescent

/-!
# Propositions as data, as types and as truth values

A second axis along which views of a proposition differ: how much of its
*verification* is kept.  For the proposition codes of
`Mettapedia.TypeTheory.Calculi.BooleanSTLC.ProofRelevance`, each of which has a
type of proofs:

* **as data**, a proposition is its code: what a program holds and can inspect;
* **as a type**, it is its type of proofs, up to equivalence: what the
  Curry–Howard reading keeps (Martin-Löf, *Intuitionistic Type Theory*, 1984);
* **as a truth value**, it is whether it has a proof: what propositional
  extensionality keeps, and what Lean's `Prop` is.

Each view forgets part of the one before, strictly.

* `asType`, `asTruth`: the two coarser views; truth factors through the type
  view (`factors_asType_asTruth`).
* **Types keep more than truth**: having at most one proof is a feature of the
  type (`factors_asType_proofUnique`) and not of the truth value
  (`proofUnique_not_factors_asTruth`): `⊤` and `⊤ ∨ ⊤` are both true, and the
  second has two proofs.
* **Data keeps more than types**: recognising the code `⊤` is not a feature of
  the type (`isTopCode_not_factors_asType`): `⊤` and `⊤ ∧ ⊤` have equivalent
  proof types.
* In the fragment without disjunction, where proofs are unique, the type view
  and the truth view identify the same codes (`sameProofType_iff_of_inFragment`).

This axis is independent of the one in `Mettapedia.Logic.Propositions.Views`,
which concerns how much of the sense and the reference of a sentence is kept.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions.Verification

open Mettapedia.TypeTheory.Calculi.BooleanSTLC
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Scope
open Mettapedia.GSLT.QuotientObservers (isTopCode)

/-- Two codes are the same proposition as types: their proof types are
equivalent. -/
def SameProofType (P Q : PropCode) : Prop :=
  Nonempty (P.Proof ≃ Q.Proof)

/-- Sameness as types is an equivalence relation. -/
def proofTypeSetoid : Setoid PropCode where
  r := SameProofType
  iseqv :=
    { refl := fun _ => ⟨Equiv.refl _⟩
      symm := fun ⟨equivalence⟩ => ⟨equivalence.symm⟩
      trans := fun ⟨first⟩ ⟨second⟩ => ⟨first.trans second⟩ }

/-- The proposition as a type, up to equivalence of proof types. -/
def asType : PropCode → Quotient proofTypeSetoid :=
  Quotient.mk proofTypeSetoid

/-- The proposition as a truth value. -/
def asTruth (P : PropCode) : Prop :=
  Nonempty P.Proof

/-- Having at most one proof. -/
def ProofUnique (P : PropCode) : Prop :=
  Subsingleton P.Proof

/-- **Truth is a feature of the type.** -/
theorem factors_asType_asTruth : Factors asType asTruth :=
  (function_descends_iff proofTypeSetoid asTruth).mpr fun _ _ ⟨equivalence⟩ =>
    propext equivalence.nonempty_congr

/-- **Uniqueness of proofs is a feature of the type.** -/
theorem factors_asType_proofUnique : Factors asType ProofUnique :=
  (function_descends_iff proofTypeSetoid ProofUnique).mpr fun _ _ ⟨equivalence⟩ =>
    propext equivalence.subsingleton_congr

/-- The witness: `⊤` and `⊤ ∨ ⊤` are both true, and only the first has a
unique proof. -/
def proofUniqueFiber : NonTrivialFiber asTruth ProofUnique :=
  .ofProp (a := PropCode.top) (b := Disjunction.twoProofs)
    (propext ⟨fun _ => ⟨Disjunction.leftProof⟩, fun _ => ⟨PUnit.unit⟩⟩)
    (PropCode.proof_subsingleton .top)
    fun unique => Disjunction.leftProof_ne_rightProof (unique.elim _ _)

/-- **Uniqueness of proofs is not a feature of the truth value.** -/
theorem proofUnique_not_factors_asTruth : ¬ Factors asTruth ProofUnique :=
  proofUniqueFiber.not_factors

/-- `⊤` and `⊤ ∧ ⊤` are the same proposition as types. -/
theorem sameProofType_top_and : SameProofType .top (.and .top .top) :=
  ⟨{ toFun := fun _ => (PUnit.unit, PUnit.unit)
     invFun := fun _ => PUnit.unit
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }⟩

/-- The witness: one type, two codes. -/
def isTopCodeFiber : NonTrivialFiber asType isTopCode where
  left := .top
  right := .and .top .top
  sameShadow := Quotient.sound sameProofType_top_and
  differentValue := Bool.noConfusion

/-- **Recognising a code is not a feature of the type.** -/
theorem isTopCode_not_factors_asType : ¬ Factors asType isTopCode :=
  isTopCodeFiber.not_factors

/-- **Where proofs are unique, the type view and the truth view identify the
same codes.** -/
theorem sameProofType_iff_of_inFragment {P Q : PropCode} (inP : P.InFragment)
    (inQ : Q.InFragment) : SameProofType P Q ↔ (asTruth P ↔ asTruth Q) := by
  constructor
  · rintro ⟨equivalence⟩
    exact equivalence.nonempty_congr
  · intro sameTruth
    have := PropCode.proof_subsingleton inP
    have := PropCode.proof_subsingleton inQ
    by_cases holds : asTruth P
    · obtain ⟨proofP⟩ := holds
      obtain ⟨proofQ⟩ := sameTruth.mp ⟨proofP⟩
      exact ⟨{ toFun := fun _ => proofQ
               invFun := fun _ => proofP
               left_inv := fun _ => Subsingleton.elim _ _
               right_inv := fun _ => Subsingleton.elim _ _ }⟩
    · have emptyP : IsEmpty P.Proof := ⟨fun proof => holds ⟨proof⟩⟩
      have emptyQ : IsEmpty Q.Proof := ⟨fun proof => holds (sameTruth.mpr ⟨proof⟩)⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩

end Mettapedia.Logic.Propositions.Verification
