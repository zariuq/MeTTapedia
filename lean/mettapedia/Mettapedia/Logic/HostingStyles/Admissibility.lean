import Mettapedia.Logic.HostingStyles.IntuitionisticShallow
import Mettapedia.Logic.HostingStyles.JudgmentsAsTypes

/-!
# Derivable and admissible rules, as the three hostings see them

A rule with premises and a conclusion is

* **derivable** in a proof system when there is a derivation of the
  conclusion from the premises as assumptions (`DerivableRule`), and
* **admissible** when the conclusion has a derivation as soon as every
  premise has one (`AdmissibleRule`).

Derivable rules are admissible (`DerivableRule.admissible`).  Adding an
admissible rule to a proof system as a new primitive rule
(`RuleSignature.withRule`) changes no theorem (`withRule_proof_iff`) and
makes the rule derivable (`withRule_derivable`).  So a rule that is
admissible and not derivable gives two proof systems with the same theorems
that differ in a derivable rule.

## What each hosting sees

* **Native.**  Both properties are statements about derivations as data:
  `DerivableRule` is the existence of a derived rule, `AdmissibleRule` is a
  closure property of the derivations.  The two systems are different rule
  signatures.
* **Judgments as types.**  A rule is derivable exactly when the framework has
  a term of the conclusion's type with a hole of each premise's type
  (`derivableRule_iff_term`).  Admissibility is not the existence of a term:
  it is a statement about which types have closed terms
  (`admissibleRule_iff_closedTerms`).
* **Shallow semantic.**  A semantics maps the extended system into its theory
  only if the rule is one of its entailments (`locallySound_withRule_iff`).
  Faithfulness, being a statement about theorems, does not tell the two
  systems apart (`valid_iff_withRule_proof`).

## The worked instance

In the intuitionistic Hilbert calculus the rule from the atom `p` to the atom
`q` is admissible (`atomRule_admissible`: `p` has no derivation) and not
derivable (`atomRule_not_derivable`: a valuation makes `p` true and `q`
false).  The calculus with that rule added, `intPlus`, has the same theorems
(`intPlus_proof_iff`) and derives the rule (`atomRule_derivable_intPlus`).

* The Kripke embedding is faithful for both (`kripke_faithful`,
  `kripke_faithful_intPlus`) and is a map of theories for the first only
  (`kripke_not_locallySound_intPlus`).
* The framework over the first has no term of type `q` with a hole of type
  `p` (`atomRule_no_term`); the framework over the second has one
  (`atomRule_term_intPlus`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Framework

universe v

namespace RuleSignature

variable {J : Type} (P : RuleSignature J) {count : Nat} (premises : Fin count → J) (conclusion : J)

/-- A rule is derivable: the conclusion has a derivation from the premises as
assumptions. -/
def DerivableRule : Prop := Nonempty (P.Open premises conclusion)

/-- A rule is admissible: the conclusion has a derivation as soon as every
premise has one. -/
def AdmissibleRule : Prop :=
  (∀ index, Nonempty (P.Proof (premises index))) → Nonempty (P.Proof conclusion)

variable {P premises conclusion}

/-- **Derivable rules are admissible.** -/
theorem DerivableRule.admissible (derivable : P.DerivableRule premises conclusion) :
    P.AdmissibleRule premises conclusion := by
  rintro each
  obtain ⟨context⟩ := derivable
  exact ⟨P.fill context fun index => Classical.choice (each index)⟩

variable (P premises conclusion)

/-! ## Adding a rule -/

/-- The positions of a rule instance of the extended system. -/
def WithRule.Position : {j : J} → P.Shape PUnit.unit j ⊕ PLift (conclusion = j) → Type
  | _, .inl old => P.Position old
  | _, .inr _ => Fin count

/-- The premises of a rule instance of the extended system. -/
def WithRule.next : {j : J} → (shape : P.Shape PUnit.unit j ⊕ PLift (conclusion = j)) →
    WithRule.Position P (count := count) conclusion shape → J
  | _, .inl old, position => P.next old position
  | _, .inr _, index => premises index

/-- **The proof system with one more primitive rule.** -/
def withRule : RuleSignature J where
  Shape := fun _ j => P.Shape PUnit.unit j ⊕ PLift (conclusion = j)
  Position := fun shape => WithRule.Position P (count := count) conclusion shape
  next := fun shape position => WithRule.next P premises conclusion shape position

/-- **The added rule is derivable in the extended system.** -/
theorem withRule_derivable : (P.withRule premises conclusion).DerivableRule premises conclusion :=
  ⟨Free.node (P.withRule premises conclusion) (.inr ⟨rfl⟩) fun index =>
    (P.withRule premises conclusion).assume index⟩

variable {P premises conclusion}

/-- Every derivation of the system is a derivation of the extended system. -/
theorem withRule_of_proof {j : J} (proof : P.Proof j) :
    Nonempty ((P.withRule premises conclusion).Proof j) := by
  induction proof using Proof.induction with
  | node shape children ih =>
      exact ⟨(P.withRule premises conclusion).node (.inl shape) fun position =>
        Classical.choice (ih position)⟩

/-- **Adding an admissible rule changes no theorem.** -/
theorem withRule_proof_iff (admissible : P.AdmissibleRule premises conclusion) (j : J) :
    Nonempty ((P.withRule premises conclusion).Proof j) ↔ Nonempty (P.Proof j) := by
  constructor
  · rintro ⟨proof⟩
    induction proof using Proof.induction with
    | node shape children ih =>
        cases shape with
        | inl old => exact ⟨P.node old fun position => Classical.choice (ih position)⟩
        | inr same =>
            obtain ⟨same⟩ := same
            subst same
            exact admissible fun index => ih index
  · rintro ⟨proof⟩
    exact withRule_of_proof proof

/-! ## The shallow view -/

section Shallow

variable {Point : Type v} (holds : Point → J → Prop)

/-- **A semantics is sound for the extended system exactly when it is sound
for the system and the rule preserves truth at each point.** -/
theorem locallySound_withRule_iff :
    LocallySound holds (P.withRule premises conclusion) ↔
      LocallySound holds P ∧
        ∀ point, (∀ index, holds point (premises index)) → holds point conclusion := by
  constructor
  · intro sound
    exact ⟨fun shape point each => sound (.inl shape) point each,
      fun point each => sound (.inr ⟨rfl⟩) point each⟩
  · rintro ⟨sound, rule⟩ j shape point each
    cases shape with
    | inl old => exact sound old point each
    | inr same =>
        obtain ⟨same⟩ := same
        subst same
        exact rule point each

/-- **Faithfulness does not tell the two systems apart.** -/
theorem valid_iff_withRule_proof {holds : Point → J → Prop}
    (faithful : ∀ j, Nonempty (P.Proof j) ↔ Valid holds j)
    (admissible : P.AdmissibleRule premises conclusion) (j : J) :
    Nonempty ((P.withRule premises conclusion).Proof j) ↔ Valid holds j :=
  (withRule_proof_iff admissible j).trans (faithful j)

/-- **Under a faithful embedding, a rule is admissible exactly when validity
of the premises gives validity of the conclusion.**  The host states
admissibility as an implication between validities. -/
theorem admissibleRule_iff_valid {holds : Point → J → Prop}
    (faithful : ∀ j, Nonempty (P.Proof j) ↔ Valid holds j) :
    P.AdmissibleRule premises conclusion ↔
      ((∀ index, Valid holds (premises index)) → Valid holds conclusion) :=
  ⟨fun admissible each => (faithful _).mp (admissible fun index => (faithful _).mpr (each index)),
    fun transfer each => (faithful _).mpr (transfer fun index => (faithful _).mp (each index))⟩

end Shallow

/-! ## The judgments-as-types view -/

variable (finitary : P.Finitary)

/-- **A rule is derivable exactly when the framework has a term of the
conclusion's type with a hole of each premise's type.** -/
theorem derivableRule_iff_term :
    P.DerivableRule premises conclusion ↔
      Nonempty (Tm finitary.signature (baseHoles premises) [] (.base conclusion)) :=
  ⟨fun ⟨context⟩ => ⟨finitary.encodeContext context⟩,
    fun ⟨term⟩ => ⟨finitary.readbackContext term⟩⟩

/-- **A judgment has a derivation exactly when its type has a closed term.**
Independence of a judgment is the emptiness of a type, which is not itself a
judgment of the framework. -/
theorem proof_iff_closedTerm (j : J) :
    Nonempty (P.Proof j) ↔ Nonempty (Closed finitary.signature (.base j)) :=
  ⟨fun ⟨proof⟩ => ⟨finitary.encodeTerm proof⟩, fun ⟨term⟩ => ⟨finitary.readback term⟩⟩

/-- **Admissibility is a statement about closed terms**: the conclusion's
type has a closed term as soon as every premise's type has one. -/
theorem admissibleRule_iff_closedTerms :
    P.AdmissibleRule premises conclusion ↔
      ((∀ index, Nonempty (Closed finitary.signature (.base (premises index)))) →
        Nonempty (Closed finitary.signature (.base conclusion))) := by
  constructor
  · intro admissible each
    obtain ⟨proof⟩ := admissible fun index => (each index).map finitary.readback
    exact ⟨finitary.encodeTerm proof⟩
  · intro closed each
    obtain ⟨term⟩ := closed fun index => (each index).map finitary.encodeTerm
    exact ⟨finitary.readback term⟩

end RuleSignature

/-! ## The worked instance -/

/-- The premise of the rule: the atom `p`. -/
def atomPremise : Fin 1 → IntFormula := fun _ => .atom 0

/-- The conclusion of the rule: the atom `q`. -/
def atomConclusion : IntFormula := .atom 1

/-- The atom `p` has no derivation. -/
theorem atom_underivable : IsEmpty (IntProof (.atom 0)) :=
  isEmpty_proof_of_countermodel truthTable_locallySound (point := fun _ => false)
    (by simp [truthTableHolds, Mettapedia.Logic.ModalCompanion.ttVal])

/-- **The rule from `p` to `q` is admissible.** -/
theorem atomRule_admissible : intSignature.AdmissibleRule atomPremise atomConclusion :=
  fun each => (each 0).elim fun proof => (atom_underivable.false proof).elim

/-- **The rule from `p` to `q` is not derivable**: a valuation makes `p`
true and `q` false, and derived rules preserve truth. -/
theorem atomRule_not_derivable : ¬ intSignature.DerivableRule atomPremise atomConclusion := by
  rintro ⟨context⟩
  obtain ⟨support, follows⟩ := truthTable_locallySound.entails intFinitary context
  have value : ((1 : ℕ) == 0) = true := follows (fun atom => atom == 0) fun _ _ => rfl
  exact absurd value (by decide)

/-- The intuitionistic calculus with the rule from `p` to `q` added. -/
def intPlus : RuleSignature IntFormula := intSignature.withRule atomPremise atomConclusion

/-- **The two calculi have the same theorems.** -/
theorem intPlus_proof_iff (φ : IntFormula) : Nonempty (intPlus.Proof φ) ↔ Nonempty (IntProof φ) :=
  RuleSignature.withRule_proof_iff atomRule_admissible φ

/-- **The rule is derivable in the extended calculus.** -/
theorem atomRule_derivable_intPlus : intPlus.DerivableRule atomPremise atomConclusion :=
  intSignature.withRule_derivable atomPremise atomConclusion

/-- The Kripke embedding is faithful for the extended calculus too. -/
theorem kripke_faithful_intPlus (φ : IntFormula) :
    Nonempty (intPlus.Proof φ) ↔ Valid kripkeHolds φ :=
  RuleSignature.valid_iff_withRule_proof kripke_faithful atomRule_admissible φ

/-- **The Kripke embedding is not sound for the rules of the extended
calculus**: at the later world of the two-world model `p` is true and `q` is
not. -/
theorem kripke_not_locallySound_intPlus : ¬ LocallySound kripkeHolds intPlus := by
  intro sound
  have rule := ((RuleSignature.locallySound_withRule_iff kripkeHolds).mp sound).2
    ⟨twoWorldModel, true⟩ fun _ => ⟨rfl, rfl⟩
  exact absurd rule.1 (by decide)

/-- **The framework over the calculus has no term of type `q` with a hole of
type `p`.** -/
theorem atomRule_no_term :
    IsEmpty (Tm intFinitary.signature (RuleSignature.baseHoles atomPremise) []
      (.base atomConclusion)) :=
  ⟨fun term => atomRule_not_derivable
    ((RuleSignature.derivableRule_iff_term intFinitary).mpr ⟨term⟩)⟩

/-- The premises of the rules of the extended calculus are numbered. -/
def intPlusFinitary : intPlus.Finitary where
  arity := fun shape => match shape with
    | .inl old => intFinitary.arity old
    | .inr _ => 1
  position := fun shape => match shape with
    | .inl old => intFinitary.position old
    | .inr _ => Equiv.refl _

/-- **The framework over the extended calculus has such a term.** -/
theorem atomRule_term_intPlus :
    Nonempty (Tm intPlusFinitary.signature (RuleSignature.baseHoles atomPremise) []
      (.base atomConclusion)) :=
  (RuleSignature.derivableRule_iff_term intPlusFinitary).mp atomRule_derivable_intPlus

#print axioms RuleSignature.withRule_proof_iff
#print axioms RuleSignature.locallySound_withRule_iff
#print axioms RuleSignature.derivableRule_iff_term
#print axioms RuleSignature.admissibleRule_iff_closedTerms
#print axioms RuleSignature.admissibleRule_iff_valid
#print axioms RuleSignature.proof_iff_closedTerm
#print axioms atomRule_admissible
#print axioms atomRule_not_derivable
#print axioms kripke_not_locallySound_intPlus
#print axioms atomRule_no_term
#print axioms atomRule_term_intPlus

end Mettapedia.Logic.HostingStyles
