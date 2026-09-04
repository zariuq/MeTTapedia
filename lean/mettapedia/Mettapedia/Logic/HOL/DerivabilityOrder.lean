import Mettapedia.Logic.HOL.Semantics.GoedelDummettCountermodel

/-!
# Derivability order for extensional higher-order natural deduction

This module separates two independent ways of strengthening the current HOL
development:

* `Derivation.ofBase` adds extensional equality principles to the underlying
  natural-deduction relation;
* inclusion of closed theories adds logical axiom schemata such as
  prelinearity or excluded middle.

The order below is stated solely in terms of theorem inclusion.  A separating
formula proves non-equivalence, but does not by itself prove that the stronger
side includes every theorem of the weaker side.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Inclusion between two judgment predicates on the same carrier. -/
def JudgmentIncluded {X : Type u} (P Q : X → Prop) : Prop :=
  ∀ {x}, P x → Q x

namespace JudgmentIncluded

theorem refl {X : Type u} (P : X → Prop) : JudgmentIncluded P P :=
  fun proof => proof

theorem trans {X : Type u} {P Q R : X → Prop}
    (hPQ : JudgmentIncluded P Q) (hQR : JudgmentIncluded Q R) :
    JudgmentIncluded P R :=
  fun proof => hQR (hPQ proof)

end JudgmentIncluded

/-- Every derivation in the small equality core is a derivation in the
extensional equality calculus.  This is independent of any logical axiom
extension. -/
theorem baseDerivation_included_extensional
    {Γ : Ctx Base} (hypotheses : List (Formula Const Γ)) :
    JudgmentIncluded
      (fun conclusion => Derivation Const hypotheses conclusion)
      (fun conclusion => ExtDerivation Const hypotheses conclusion) :=
  fun proof => ExtDerivation.ofBase proof

namespace ClosedTheorySet

/-- Theorem inclusion between closed theories over one fixed typed language. -/
def DerivabilityIncluded (T U : ClosedTheorySet Const) : Prop :=
  ∀ {formula}, Provable (Const := Const) T formula →
    Provable (Const := Const) U formula

/-- Equality of theorem sets, without identifying their axiom presentations. -/
def DerivabilityEquivalent (T U : ClosedTheorySet Const) : Prop :=
  DerivabilityIncluded T U ∧ DerivabilityIncluded U T

/-- A concrete formula separating the theorem sets of two theories. -/
def Separates (T U : ClosedTheorySet Const)
    (formula : ClosedFormula Const) : Prop :=
  Provable (Const := Const) U formula ∧
    ¬ Provable (Const := Const) T formula

/-- Proper theorem extension: inclusion plus a formula newly derivable on the
right.  The inclusion field is essential; separation alone is not an order
claim. -/
def ProperDerivabilityExtension (T U : ClosedTheorySet Const) : Prop :=
  DerivabilityIncluded T U ∧ ∃ formula, Separates T U formula

namespace DerivabilityIncluded

theorem refl (T : ClosedTheorySet Const) : DerivabilityIncluded T T :=
  fun proof => proof

theorem trans {T U V : ClosedTheorySet Const}
    (hTU : DerivabilityIncluded T U) (hUV : DerivabilityIncluded U V) :
    DerivabilityIncluded T V :=
  fun proof => hUV (hTU proof)

theorem of_subset {T U : ClosedTheorySet Const} (hTU : T ⊆ U) :
    DerivabilityIncluded T U := by
  intro formula proof
  exact provable_mono (fun {_} membership => hTU membership) proof

theorem empty (T : ClosedTheorySet Const) :
    DerivabilityIncluded (∅ : ClosedTheorySet Const) T :=
  of_subset (Set.empty_subset T)

end DerivabilityIncluded

namespace DerivabilityEquivalent

theorem refl (T : ClosedTheorySet Const) : DerivabilityEquivalent T T :=
  ⟨DerivabilityIncluded.refl T, DerivabilityIncluded.refl T⟩

theorem symm {T U : ClosedTheorySet Const}
    (h : DerivabilityEquivalent T U) : DerivabilityEquivalent U T :=
  ⟨h.2, h.1⟩

theorem trans {T U V : ClosedTheorySet Const}
    (hTU : DerivabilityEquivalent T U)
    (hUV : DerivabilityEquivalent U V) :
    DerivabilityEquivalent T V :=
  ⟨DerivabilityIncluded.trans hTU.1 hUV.1,
    DerivabilityIncluded.trans hUV.2 hTU.2⟩

end DerivabilityEquivalent

theorem Separates.not_equivalent {T U : ClosedTheorySet Const}
    {formula : ClosedFormula Const} (h : Separates T U formula) :
    ¬ DerivabilityEquivalent T U := by
  intro equivalent
  exact h.2 (equivalent.2 h.1)

theorem ProperDerivabilityExtension.not_equivalent
    {T U : ClosedTheorySet Const}
    (h : ProperDerivabilityExtension T U) :
    ¬ DerivabilityEquivalent T U := by
  obtain ⟨_included, formula, separated⟩ := h
  exact separated.not_equivalent

end ClosedTheorySet

namespace AxiomExtensionOrder

open ClosedTheorySet
open HeytingSem.GoedelDummett
open KripkeHenkin
open WithParams

/-- The EM-free calculus embeds in its prelinearity-schema extension. -/
theorem emFree_included_prelinear :
    DerivabilityIncluded
      (∅ : ClosedTheorySet (WithParams Const))
      (lcSchema (Base := Base) Const) :=
  DerivabilityIncluded.empty _

/-- The EM-free calculus embeds in its excluded-middle-schema extension. -/
theorem emFree_included_excludedMiddle :
    DerivabilityIncluded
      (∅ : ClosedTheorySet (WithParams Const))
      (EMSchema (Base := Base) Const) :=
  DerivabilityIncluded.empty _

/-- The distinguished excluded-middle instance is an actual theorem of the
excluded-middle schema theory. -/
theorem emCanary_provable_excludedMiddle :
    Provable (Const := WithParams EMCanaryConst)
      (EMSchema (Base := EMCanaryBase) EMCanaryConst)
      emCanaryExcludedMiddleLC := by
  exact provable_of_mem
    (emClosed_mem (Base := EMCanaryBase) (Const := EMCanaryConst)
      emCanaryAtomLC)

/-- The same instance is not a theorem of the EM-free calculus over the
parameter language.  The proof factors through the stronger prelinearity
extension, where the existing linear Kripke countermodel already refutes it. -/
theorem emCanary_not_provable_emFree :
    ¬ Provable (Const := WithParams EMCanaryConst)
      (∅ : ClosedTheorySet (WithParams EMCanaryConst))
      emCanaryExcludedMiddleLC := by
  intro emFreeProof
  apply em_not_derivable_LC
  exact provable_mono
    (T := (∅ : ClosedTheorySet (WithParams EMCanaryConst)))
    (U := (∅ : ClosedTheorySet (WithParams EMCanaryConst)) ∪
      lcSchema (Base := EMCanaryBase) EMCanaryConst)
    (fun {_formula} member => Set.mem_union_left _ member)
    emFreeProof

/-- Excluded middle is a proper theorem extension of the current EM-free
extensional calculus, witnessed on the parameter-extended canary language. -/
theorem emFree_proper_excludedMiddle :
    ProperDerivabilityExtension
      (∅ : ClosedTheorySet (WithParams EMCanaryConst))
      (EMSchema (Base := EMCanaryBase) EMCanaryConst) :=
  ⟨emFree_included_excludedMiddle,
    ⟨emCanaryExcludedMiddleLC,
      emCanary_provable_excludedMiddle, emCanary_not_provable_emFree⟩⟩

/-- Excluded middle separates its schema theory from the prelinearity theory.
This is deliberately a separation theorem, not an unproved global inclusion
claim between the two theories. -/
theorem excludedMiddle_separates_prelinear :
    Separates
      (lcSchema (Base := EMCanaryBase) EMCanaryConst)
      (EMSchema (Base := EMCanaryBase) EMCanaryConst)
      emCanaryExcludedMiddleLC := by
  refine ⟨emCanary_provable_excludedMiddle, ?_⟩
  simpa [ProvableLC] using em_not_derivable_LC

/-- Consequently, the prelinearity and excluded-middle schema theories do not
have the same theorems. -/
theorem prelinear_not_equivalent_excludedMiddle :
    ¬ DerivabilityEquivalent
      (lcSchema (Base := EMCanaryBase) EMCanaryConst)
      (EMSchema (Base := EMCanaryBase) EMCanaryConst) :=
  excludedMiddle_separates_prelinear.not_equivalent

end AxiomExtensionOrder

end Mettapedia.Logic.HOL
