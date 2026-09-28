import Foundation.Modal.ModalCompanion.Standard.Int
import Mettapedia.Logic.ModalCompanion.GoedelReverseTranslation

/-!
# Faithfulness of Gödel's modal translation, by Gödel's 1941 syntactic proof

Gödel's translation `U` of intuitionistic into modal formulas is Foundation's
`Propositional.Formula.gödelTranslate` (`φᵍ`): `U(p) = □p`, `U(A ⊃ C) = □(U(A) ⊃ U(C))`,
`U(A ∧ C) = U(A) ∧ U(C)`, `U(A ∨ C) = U(A) ∨ U(C)`. Gödel's language has negation
`U(¬A) = □¬U(A)`; in Foundation `¬A` is `A ➝ ⊥` and `⊥ᵍ = ⊥`, so `(¬A)ᵍ = □¬(Aᵍ)` holds by
definition (`gödelTranslate_neg`) and the two translations agree.

## History

In 1933 Gödel observed that `Int ⊢ A` implies `S4 ⊢ U(A)`, reading `□A` as "`A` is
provable" in an informal, absolute sense, and conjectured the converse. McKinsey and Tarski
proved the converse in 1948 by algebraic (topological) semantics, where `□` is the interior
operator of a topological space; Foundation proves it by Kripke semantics (its instance
`Modal.ModalCompanion Propositional.Int Modal.S4`). In 1941 Gödel found a syntactic proof,
recorded in his notebook *Resultate Grundlagen* (Theorems 62–64) and published in *Results on
Foundations* (2023); Negri and von Plato reconstruct it and extend it to derivations from
assumptions. The proof reads modal formulas back into intuitionistic ones through
distinguished matrices (`GoedelReverseTranslation`), and uses Theorem 62, the propositional
case of the theorem Barr proved for geometric theories in 1974 by topos theory and Negri
proved in 2003 by proof analysis (`GeometricBarr`).

Nothing here concerns a formal provability predicate: `□` is the operator of the modal
calculus S4, read as informal provability or as topological interior, and for provability in
a formal theory the axiom `□A ⊃ A` is not available (Gödel already noted this in 1933); no
reflection principle follows. Nor does anything here concern first-order logic.

## Main results

* `gödelStable`: `U(A) ⊃ □U(A)` in S4, derivation-producing.
* `reverseTranslate_gödel` (Lemma 9): `U(A)′ ≡ A` intuitionistically.
* `s4GödelToInt` (**Theorem 64** as a proof transformation): an S4 derivation of `U(A)` from
  assumptions `U(Γ)` becomes an intuitionistic derivation of `A` from `Γ`; `s4GödelToIntDeriv`
  is the version for derivation trees and `provable_of_provable_gödelTranslate` the version
  for Foundation's systems: `Modal.S4 ⊢ φᵍ → Propositional.Int ⊢ φ`.
* `intToS4` (Gödel 1933) as a proof transformation, and `modalCompanion_Int_S4`,
  `modalCompanion_Int_S4_syntactic`: Foundation's `Modal.ModalCompanion Propositional.Int
  Modal.S4`, from Theorem 64 with Foundation's `gS4_of_Int` and with `intToS4` respectively.

## References

* K. Gödel, *Eine Interpretation des intuitionistischen Aussagenkalküls*, Ergebnisse eines
  mathematischen Kolloquiums 4 (1933), 39–40.
* J. C. C. McKinsey and A. Tarski, *Some theorems about the sentential calculi of Lewis and
  Heyting*, J. Symbolic Logic 13 (1948), 1–15.
* K. Gödel, *Results on Foundations*, M. Hämeen-Anttila and J. von Plato (eds.), Springer,
  2023.
* S. Negri and J. von Plato, *Intuitionistic and modal logic in Gödel's Resultate
  Grundlagen*, Logique et Analyse 268, 439–465, doi:10.2143/LEA.268.0.3295055.
* J. von Plato, *Gödel's modal interpretation of intuitionistic logic and its proof theory*,
  Monatsh. Math. 208 (2025), 791–817, doi:10.1007/s00605-025-02083-0.
* M. Barr, *Toposes without points*, J. Pure Appl. Algebra 5 (1974), 265–280.
* S. Negri, *Contraction-free sequent calculi for geometric theories with an application to
  Barr's theorem*, Arch. Math. Logic 42 (2003), 389–401.
* S. Negri and J. von Plato, *Proof Analysis*, Cambridge University Press, 2011.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalCompanion

open LO LO.Entailment LO.Modal.Entailment
open Propositional.Formula (gödelTranslate)

/-- Gödel's clause `U(¬A) = □¬U(A)` holds by definition. -/
theorem gödelTranslate_neg (φ : Propositional.Formula ℕ) : (∼φ)ᵍ = □(∼(φᵍ)) := rfl

/-! ## S4 facts about translated formulas -/

section S4Facts

variable {S : Type*} [Entailment S (Modal.Formula ℕ)] (𝓢 : S) [Modal.Entailment.S4 𝓢]

/-- Translated formulas are stable in S4: `U(A) ⊃ □U(A)`. -/
def gödelStable : (φ : Propositional.Formula ℕ) → 𝓢 ⊢! φᵍ ➝ □φᵍ
  | .atom _ => axiomFour
  | .falsum => efq
  | .and φ ψ => C_trans (CKK_of_C_of_C (gödelStable φ) (gödelStable ψ)) collect_box_and
  | .or φ ψ =>
    left_A_intro (C_trans (gödelStable φ) (axiomK' (nec or₁)))
      (C_trans (gödelStable ψ) (axiomK' (nec or₂)))
  | .imp _ _ => axiomFour

/-- `U(A) ∨ U(C) ⊃ □U(A) ∨ □U(C)`. -/
def gödelOrToBoxOr (φ ψ : Propositional.Formula ℕ) : 𝓢 ⊢! φᵍ ⋎ ψᵍ ➝ □φᵍ ⋎ □ψᵍ :=
  CAA_of_C_of_C (gödelStable 𝓢 φ) (gödelStable 𝓢 ψ)

/-- `□U(A) ∨ □U(C) ⊃ U(A) ∨ U(C)`. -/
def boxOrToGödelOr (φ ψ : Propositional.Formula ℕ) : 𝓢 ⊢! □φᵍ ⋎ □ψᵍ ➝ φᵍ ⋎ ψᵍ :=
  CAA_of_C_of_C axiomT axiomT

/-- `(U(A) ⊃ U(C)) ⊃ (□U(A) ⊃ □U(C))`. -/
def gödelImpToBoxImp (φ ψ : Propositional.Formula ℕ) :
    𝓢 ⊢! (φᵍ ➝ ψᵍ) ➝ (□φᵍ ➝ □ψᵍ) :=
  C_trans (CCC_of_C_left axiomT) (CCC_of_C_right (gödelStable 𝓢 ψ))

/-- `(□U(A) ⊃ □U(C)) ⊃ (U(A) ⊃ U(C))`. -/
def boxImpToGödelImp (φ ψ : Propositional.Formula ℕ) :
    𝓢 ⊢! (□φᵍ ➝ □ψᵍ) ➝ (φᵍ ➝ ψᵍ) :=
  C_trans (CCC_of_C_left (gödelStable 𝓢 φ)) (CCC_of_C_right axiomT)

end S4Facts

/-! ## Lemma 9 and Theorem 64 -/

section Faithfulness

variable {S : Type*} [Entailment S (Propositional.Formula ℕ)] (𝓢 : S) [Entailment.Int 𝓢]

/-- The S4 derivation trees of the facts above, with no assumptions. -/
abbrev s4 : S4H := ⟨[]⟩

/-- **Lemma 9**: `U(A)′ ≡ A` intuitionistically. For `∨` and `⊃` the translated formulas are
first replaced by S4-equivalent boxed ones (using `gödelStable` and Theorem 63 through
`reverseTranslate_mono`), to which Lemmas 7 and 8 apply. -/
def reverseTranslate_gödel : (φ : Propositional.Formula ℕ) → 𝓢 ⊢! reverseTranslate (φᵍ) ⭤ φ
  | .atom _ => E_Id
  | .falsum => reverseTranslate_bot 𝓢
  | .and φ ψ =>
    E_trans (reverseTranslate_and 𝓢 (φᵍ) (ψᵍ))
      (EKK_of_E_of_E (reverseTranslate_gödel φ) (reverseTranslate_gödel ψ))
  | .or φ ψ =>
    E_trans
      (E_intro (reverseTranslate_mono 𝓢 (gödelOrToBoxOr s4 φ ψ))
        (reverseTranslate_mono 𝓢 (boxOrToGödelOr s4 φ ψ)))
      (E_trans (reverseTranslate_or_box 𝓢 (φᵍ) (ψᵍ))
        (EAA_of_E_of_E (reverseTranslate_gödel φ) (reverseTranslate_gödel ψ)))
  | .imp φ ψ =>
    (E_trans
      (E_intro (reverseTranslate_mono 𝓢 (gödelImpToBoxImp s4 φ ψ))
        (reverseTranslate_mono 𝓢 (boxImpToGödelImp s4 φ ψ)))
      (E_trans (reverseTranslate_imp_box 𝓢 (φᵍ) (ψᵍ))
        (ECC_of_E_of_E (reverseTranslate_gödel φ) (reverseTranslate_gödel ψ))) :
      𝓢 ⊢! reverseTranslate (φᵍ ➝ ψᵍ) ⭤ (φ ➝ ψ))

/-- **Gödel's Theorem 64**, as a proof transformation: an S4 derivation of `U(A)` from the
assumptions `U(Γ)` becomes a derivation of `A` in `𝓢`, given derivations in `𝓢` of the
assumptions `Γ`. The transformation is Theorem 63 (`s4ToInt`) followed by Lemma 9. -/
def s4GödelToInt {Γ : List (Propositional.Formula ℕ)}
    (hyps : (γ : Propositional.Formula ℕ) → γ ∈ Γ → 𝓢 ⊢! γ) {φ : Propositional.Formula ℕ}
    (d : S4Deriv (Γ.map gödelTranslate) (φᵍ)) : 𝓢 ⊢! φ :=
  K_left (reverseTranslate_gödel 𝓢 φ) ⨀ s4ToInt 𝓢 (fun δ hδ =>
    let γ := Γ.chooseX (fun γ => γᵍ = δ) (List.mem_map.mp hδ)
    γ.2.2 ▸ (K_right (reverseTranslate_gödel 𝓢 γ.1) ⨀ hyps γ.1 γ.2.1)) d

end Faithfulness

/-- **Gödel's Theorem 64** for derivation trees: an S4 derivation of `U(A)` from `U(Γ)` (with
necessitation applicable to derived formulas) becomes an intuitionistic derivation of `A` from
the assumptions `Γ`. -/
def s4GödelToIntDeriv {Γ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ}
    (d : S4Deriv (Γ.map gödelTranslate) (φᵍ)) : IntDeriv Γ φ :=
  s4GödelToInt (⟨Γ⟩ : IntH) (fun _ h => PropDeriv.hyp h) d

/-- **Gödel's Theorem 64** for Foundation's systems: `S4 ⊢ U(A)` implies `Int ⊢ A`. -/
theorem provable_of_provable_gödelTranslate {φ : Propositional.Formula ℕ}
    (h : Modal.S4 ⊢ φᵍ) : Propositional.Int ⊢ φ :=
  (S4Deriv.nonempty_of_provable h).elim fun d =>
    ⟨s4GödelToInt Propositional.Int (Γ := []) (fun _ h => absurd h List.not_mem_nil) d⟩

/-! ## The embedding direction (Gödel 1933) and the modal companion -/

section Embedding

variable {S : Type*} [Entailment S (Modal.Formula ℕ)] (𝓢 : S) [Modal.Entailment.S4 𝓢]

/-- Gödel's 1933 direction, as a proof transformation: an intuitionistic derivation of `A`
from `Γ` becomes an S4 derivation of `U(A)` in `𝓢`, given derivations of `U(Γ)`. Modus
ponens uses the axiom T; necessitation is only applied to closed derivations. -/
def intToS4 {Γ : List (Propositional.Formula ℕ)}
    (hyps : (γ : Propositional.Formula ℕ) → γ ∈ Γ → 𝓢 ⊢! γᵍ) :
    {φ : Propositional.Formula ℕ} → IntDeriv Γ φ → 𝓢 ⊢! φᵍ
  | _, .hyp h => hyps _ h
  | _, .efq _ => nec efq
  | _, .lem _ h => nomatch h
  | _, .implyK φ _ => nec (C_trans (gödelStable 𝓢 φ) (axiomK' (nec implyK)))
  | _, .implyS _ _ _ =>
    nec (C_trans (C_trans (axiomK' (nec (CCC_of_C_right axiomT))) axiomFour)
      (axiomK' (nec (C_trans (axiomK' (nec implyS)) axiomK))))
  | _, .andElimL _ _ => nec and₁
  | _, .andElimR _ _ => nec and₂
  | _, .andIntro φ _ => nec (C_trans (gödelStable 𝓢 φ) (axiomK' (nec and₃)))
  | _, .orIntroL _ _ => nec or₁
  | _, .orIntroR _ _ => nec or₂
  | _, .orElim _ _ _ =>
    nec (C_trans axiomFour (axiomK' (nec (C_trans (axiomK' (nec or₃)) axiomK))))
  | _, .mdp d₁ d₂ => axiomT ⨀ intToS4 hyps d₁ ⨀ intToS4 hyps d₂

end Embedding

/-- Gödel's 1933 direction for derivation trees. -/
def intToS4Deriv {Γ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ}
    (d : IntDeriv Γ φ) : S4Deriv (Γ.map gödelTranslate) (φᵍ) :=
  intToS4 (⟨Γ.map gödelTranslate⟩ : S4H) (fun _ h => S4Deriv.hyp (List.mem_map_of_mem h)) d

/-- Gödel's 1933 direction for Foundation's systems, through derivation trees. -/
theorem provable_gödelTranslate_of_provable {φ : Propositional.Formula ℕ}
    (h : Propositional.Int ⊢ φ) : Modal.S4 ⊢ φᵍ :=
  (IntDeriv.nonempty_of_provable h).elim fun d => (intToS4Deriv d).provable

/-- Foundation's `Modal.ModalCompanion Propositional.Int Modal.S4`, obtained from Gödel's
syntactic Theorem 64 and Foundation's embedding direction `gS4_of_Int`, independently of
Foundation's Kripke-semantic proof. -/
theorem modalCompanion_Int_S4 : Modal.ModalCompanion Propositional.Int Modal.S4 :=
  Modal.instModalCompanion Modal.gS4_of_Int provable_of_provable_gödelTranslate

/-- Foundation's `Modal.ModalCompanion Propositional.Int Modal.S4`, with both directions
obtained from proof transformations on derivation trees. -/
theorem modalCompanion_Int_S4_syntactic : Modal.ModalCompanion Propositional.Int Modal.S4 :=
  Modal.instModalCompanion provable_gödelTranslate_of_provable
    provable_of_provable_gödelTranslate

end Mettapedia.Logic.ModalCompanion
