import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidence
import Mettapedia.TypeTheory.DependentFamilySectionDescent
import Mathlib.Data.Quot

/-!
# Dependent consumers of extensional facts and retained derivations

The fact quotient identifies receipts with the same conclusion. Its elements
contain no chosen derivation. Dependent quotient elimination nevertheless
constructs every compatible consumer: after interpreting its fibre, the
consumer must return the same dependent value on every pair of receipts with
the same fact. This gives both inverse section laws and an exact descent
criterion, without an operation choosing a proof from mere provability.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence

attribute [local instance] Finite.membership

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe u v w
variable {Atom : Type u} {Origin : Type v} (source : Source Atom Origin)

def factKernel : Setoid (Receipt source) := Setoid.ker Receipt.fact

abbrev Facts := Quotient (factKernel source)

def observeFact (receipt : Receipt source) : Facts source := Quotient.mk _ receipt

def factValue : Facts source → Atom :=
  Quotient.lift Receipt.fact (fun _ _ same => same)

@[simp] theorem factValue_observeFact (receipt : Receipt source) :
    factValue source (observeFact source receipt) = receipt.fact := rfl

theorem observeFact_eq_iff (first second : Receipt source) :
    observeFact source first = observeFact source second ↔ first.fact = second.fact :=
  Quotient.eq

theorem factValue_injective : Function.Injective (factValue source) := by
  intro first second
  induction first using Quotient.inductionOn with
  | h first =>
      induction second using Quotient.inductionOn with
      | h second =>
          intro same
          exact Quotient.sound (s := factKernel source) same

section Dependent

variable {source} {family : Receipt source → Type w}
variable (d : FamilyFactorization Receipt.fact family)

def factFamily (value : Facts source) : Type w := d.targetFamily (factValue source value)

/-- The same actual fibre interpretation factors through the fact quotient. -/
def quotientFamily : FamilyFactorization (observeFact source) family where
  targetFamily := factFamily d
  identify := d.identify

/-- A complete section is formed by dependent quotient elimination. -/
def descend (term : ∀ receipt, family receipt) (compatible : Compatible d term)
    (value : Facts source) : factFamily d value :=
  Quotient.hrecOn' (φ := factFamily d) value
    (fun receipt => d.identify receipt (term receipt))
    (fun first second same =>
      (Sigma.mk.inj_iff.mp (compatible first second same)).2)

@[simp] theorem descend_observeFact (term : ∀ receipt, family receipt)
    (compatible : Compatible d term) (receipt : Receipt source) :
    descend d term compatible (observeFact source receipt) =
      d.identify receipt (term receipt) := rfl

def pullback (term : ∀ value, factFamily d value) (receipt : Receipt source) : family receipt :=
  (d.identify receipt).symm (term (observeFact source receipt))

theorem pullback_compatible (term : ∀ value, factFamily d value) :
    Compatible d (pullback d term) := by
  intro first second same
  have classes : observeFact source first = observeFact source second := Quotient.sound same
  have pair := congrArg (fun value : Facts source =>
    (⟨factValue source value, term value⟩ : Sigma d.targetFamily)) classes
  change (⟨first.fact, d.identify first ((d.identify first).symm
    (term (observeFact source first)))⟩ : Sigma d.targetFamily) =
    ⟨second.fact, d.identify second ((d.identify second).symm
      (term (observeFact source second)))⟩
  exact (congrArg (fun value : d.targetFamily first.fact =>
    (⟨first.fact, value⟩ : Sigma d.targetFamily)) ((d.identify first).apply_symm_apply _)).trans
      (pair.trans (congrArg (fun value : d.targetFamily second.fact =>
        (⟨second.fact, value⟩ : Sigma d.targetFamily))
          ((d.identify second).apply_symm_apply _)).symm)

@[simp] theorem pullback_descend (term : ∀ receipt, family receipt)
    (compatible : Compatible d term) : pullback d (descend d term compatible) = term := by
  funext receipt
  exact (d.identify receipt).symm_apply_apply (term receipt)

@[simp] theorem descend_pullback (term : ∀ value, factFamily d value) :
    descend d (pullback d term) (pullback_compatible d term) = term := by
  funext value
  induction value using Quotient.inductionOn with
  | h receipt => exact (d.identify receipt).apply_symm_apply _

/-- Exactly the compatible dependent consumers can use the fact quotient. -/
theorem compatible_iff_descends (term : ∀ receipt, family receipt) :
    Compatible d term ↔ ∃ summary : ∀ value, factFamily d value, pullback d summary = term := by
  constructor
  · intro compatible
    exact ⟨descend d term compatible, pullback_descend d term compatible⟩
  · rintro ⟨summary, same⟩
    exact same ▸ pullback_compatible d summary

def compatibleSectionEquiv :
    {term : ∀ receipt, family receipt // Compatible d term} ≃
      (∀ value, factFamily d value) where
  toFun term := descend d term.1 term.2
  invFun summary := ⟨pullback d summary, pullback_compatible d summary⟩
  left_inv term := Subtype.ext (pullback_descend d term.1 term.2)
  right_inv := descend_pullback d

theorem descend_unique (term : ∀ receipt, family receipt) (compatible : Compatible d term)
    (summary : ∀ value, factFamily d value) (agrees : pullback d summary = term) :
    summary = descend d term compatible := by
  funext value
  induction value using Quotient.inductionOn with
  | h receipt =>
      have atReceipt := congrFun agrees receipt
      exact ((d.identify receipt).apply_symm_apply _).symm.trans
        (congrArg (d.identify receipt) atReceipt)

end Dependent

end Mettapedia.GSLT.ProgrammableSpaceEvidence
