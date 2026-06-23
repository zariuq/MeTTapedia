import Mettapedia.OSLF.Formula
import Foundation.Modal.Kripke.AxiomGeach

/-!
# OSLF ↔ Foundation Kripke Bridge

Connects OSLF's Kripke-style modal semantics to the Foundation library's
formal Kripke framework, enabling reuse of Foundation's proven meta-theory
(soundness, completeness, frame correspondence for K/S4/S5/GL/...).

## Key Direction Mismatch

OSLF is a **tense logic**: `◇` looks forward along R, `□` looks backward.
Foundation uses forward for both. We bridge with two frames per relation:
- **Forward frame** (`Rel := R`): for the ◇ fragment
- **Converse frame** (`Rel := Rᵒᵖ`): for the □ fragment

All theorems proven (0 sorry).

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
- Foundation library (Igarashi et al.)
-/

namespace Mettapedia.Logic.OSLFKripkeBridge

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.Formula (OSLFFormula AtomSem sem)

open LO.Modal
open LO.Modal.Kripke

/-! ## Nonempty Pattern -/

instance : Nonempty Pattern := ⟨.bvar 0⟩

/-! ## Atom Encoding -/

/-- Parametric atom encoding from OSLF's String atoms to Foundation's ℕ atoms.
The `decode_encode` field guarantees injectivity. -/
structure AtomEncoding where
  encode : String → ℕ
  decode : ℕ → Option String
  decode_encode : ∀ s, decode (encode s) = some s

theorem AtomEncoding.encode_injective (enc : AtomEncoding) :
    Function.Injective enc.encode := by
  intro s₁ s₂ h
  have h₁ := enc.decode_encode s₁
  have h₂ := enc.decode_encode s₂
  rw [h] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## Frame and Model Construction -/

/-- Forward Kripke frame: `Rel := R`. For bridging OSLF ◇. -/
def oslfForwardFrame (R : Pattern → Pattern → Prop) : Frame where
  World := Pattern
  Rel := R

/-- Converse Kripke frame: `Rel := Rᵒᵖ`. For bridging OSLF □. -/
def oslfConverseFrame (R : Pattern → Pattern → Prop) : Frame where
  World := Pattern
  Rel := fun x y => R y x

/-- Kripke model on the forward frame with atom semantics from OSLF. -/
def oslfForwardModel (R : Pattern → Pattern → Prop) (I : AtomSem)
    (enc : AtomEncoding) : Model where
  toFrame := oslfForwardFrame R
  Val := fun n p => match enc.decode n with
    | some s => I s p
    | none => False

/-- Kripke model on the converse frame with atom semantics from OSLF. -/
def oslfConverseModel (R : Pattern → Pattern → Prop) (I : AtomSem)
    (enc : AtomEncoding) : Model where
  toFrame := oslfConverseFrame R
  Val := fun n p => match enc.decode n with
    | some s => I s p
    | none => False

/-! ## Formula Translation -/

/-- Translate OSLF formula to Foundation modal formula.
Maps each OSLF connective to its Foundation counterpart.
The semantics of □ differ by frame choice (forward vs converse). -/
def translateForward (enc : AtomEncoding) : OSLFFormula → Formula ℕ
  | .top => Formula.imp Formula.falsum Formula.falsum
  | .bot => Formula.falsum
  | .atom s => Formula.atom (enc.encode s)
  | .and φ ψ => Formula.neg (Formula.imp (translateForward enc φ) (Formula.neg (translateForward enc ψ)))
  | .or φ ψ => Formula.imp (Formula.neg (translateForward enc φ)) (translateForward enc ψ)
  | .imp φ ψ => Formula.imp (translateForward enc φ) (translateForward enc ψ)
  | .dia φ => Formula.neg (Formula.box (Formula.neg (translateForward enc φ)))
  | .box φ => Formula.box (translateForward enc φ)

/-! ## Fragment Predicates -/

/-- Diamond-only formulas: no `.box` subformulas.
On the forward frame, these have exact semantic correspondence. -/
def diaOnly : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => diaOnly φ ∧ diaOnly ψ
  | .dia φ => diaOnly φ
  | .box _ => False

/-- Box-only formulas: no `.dia` subformulas.
On the converse frame, these have exact semantic correspondence. -/
def boxOnly : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => boxOnly φ ∧ boxOnly ψ
  | .box φ => boxOnly φ
  | .dia _ => False

/-- Modal-free formulas are both diaOnly and boxOnly. -/
def modalFree : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => modalFree φ ∧ modalFree ψ
  | .dia _ | .box _ => False

theorem modalFree_diaOnly {φ : OSLFFormula} (h : modalFree φ) : diaOnly φ := by
  induction φ with
  | top | bot | atom _ => trivial
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | imp _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | dia _ => exact absurd h (by simp [modalFree])
  | box _ => exact absurd h (by simp [modalFree])

theorem modalFree_boxOnly {φ : OSLFFormula} (h : modalFree φ) : boxOnly φ := by
  induction φ with
  | top | bot | atom _ => trivial
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | imp _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | dia _ => exact absurd h (by simp [modalFree])
  | box _ => exact absurd h (by simp [modalFree])

/-! ## Core Correspondence Theorems -/

/-- **Forward correspondence**: for diamond-only formulas, OSLF `sem` on relation R
coincides with Foundation `Satisfies` on the forward frame. -/
theorem sem_iff_satisfies_forward (enc : AtomEncoding)
    (R : Pattern → Pattern → Prop) (I : AtomSem)
    {φ : OSLFFormula} (hdia : diaOnly φ) (p : Pattern) :
    sem R I φ p ↔
    Formula.Kripke.Satisfies (oslfForwardModel R I enc) p (translateForward enc φ) := by
  induction φ generalizing p with
  | top =>
    -- OSLF: True; Foundation: (⊥ → ⊥) which is True
    simp [sem, translateForward, Formula.Kripke.Satisfies]
  | bot =>
    simp [sem, translateForward, Formula.Kripke.Satisfies]
  | atom s =>
    -- OSLF: I s p; Foundation: M.Val p (enc.encode s) = I s p (by decode_encode)
    simp only [sem, translateForward, Formula.Kripke.Satisfies,
               oslfForwardModel, enc.decode_encode]
  | imp φ ψ ihφ ihψ =>
    -- Both sides are implications
    simp only [sem, translateForward, Formula.Kripke.Satisfies]
    exact ⟨fun h hφ => (ihψ hdia.2 p).mp (h ((ihφ hdia.1 p).mpr hφ)),
           fun h hφ => (ihψ hdia.2 p).mpr (h ((ihφ hdia.1 p).mp hφ))⟩
  | and φ ψ ihφ ihψ =>
    -- OSLF: φ ∧ ψ; Foundation: ¬(φ → ¬ψ) which is ¬(φ → (ψ → ⊥))
    simp only [sem, translateForward, Formula.Kripke.Satisfies]
    constructor
    · intro ⟨h₁, h₂⟩ hcontra
      exact hcontra ((ihφ hdia.1 p).mp h₁) ((ihψ hdia.2 p).mp h₂)
    · intro h
      constructor
      · by_contra hφ
        exact h (fun hφ' _ => hφ ((ihφ hdia.1 p).mpr hφ'))
      · by_contra hψ
        exact h (fun _ hψ' => hψ ((ihψ hdia.2 p).mpr hψ'))
  | or φ ψ ihφ ihψ =>
    -- OSLF: φ ∨ ψ; Foundation: ¬φ → ψ which is (φ → ⊥) → ψ
    simp only [sem, translateForward, Formula.Kripke.Satisfies]
    constructor
    · intro h hnφ
      cases h with
      | inl hφ => exact absurd ((ihφ hdia.1 p).mp hφ) hnφ
      | inr hψ => exact (ihψ hdia.2 p).mp hψ
    · intro h
      by_cases hφ : sem R I φ p
      · exact Or.inl hφ
      · exact Or.inr ((ihψ hdia.2 p).mpr (h (fun hφ' => hφ ((ihφ hdia.1 p).mpr hφ'))))
  | dia φ ih =>
    -- OSLF: ∃ q, R p q ∧ φ q; Foundation: ¬□¬φ = ¬(∀ y, p ≺ y → ¬φ y)
    simp only [sem, translateForward, Formula.Kripke.Satisfies,
               oslfForwardModel, oslfForwardFrame, Frame.Rel']
    constructor
    · intro ⟨q, hRpq, hq⟩ hbox
      exact hbox q hRpq ((ih hdia q).mp hq)
    · intro h
      by_contra hnoex
      push_neg at hnoex
      exact h (fun q hRpq hq => by
        have := (ih hdia q).mpr hq
        exact absurd this (hnoex q hRpq))
  | box _ => exact absurd hdia (by simp [diaOnly])

/-- **Converse correspondence**: for box-only formulas, OSLF `sem` on relation R
coincides with Foundation `Satisfies` on the converse frame (Rᵒᵖ). -/
theorem sem_iff_satisfies_converse (enc : AtomEncoding)
    (R : Pattern → Pattern → Prop) (I : AtomSem)
    {φ : OSLFFormula} (hbox : boxOnly φ) (p : Pattern) :
    sem R I φ p ↔
    Formula.Kripke.Satisfies (oslfConverseModel R I enc) p (translateForward enc φ) := by
  induction φ generalizing p with
  | top => simp [sem, translateForward, Formula.Kripke.Satisfies]
  | bot => simp [sem, translateForward, Formula.Kripke.Satisfies]
  | atom s =>
    simp only [sem, translateForward, Formula.Kripke.Satisfies,
               oslfConverseModel, enc.decode_encode]
  | imp φ ψ ihφ ihψ =>
    simp only [sem, translateForward, Formula.Kripke.Satisfies]
    exact ⟨fun h hφ => (ihψ hbox.2 p).mp (h ((ihφ hbox.1 p).mpr hφ)),
           fun h hφ => (ihψ hbox.2 p).mpr (h ((ihφ hbox.1 p).mp hφ))⟩
  | and φ ψ ihφ ihψ =>
    simp only [sem, translateForward, Formula.Kripke.Satisfies]
    constructor
    · intro ⟨h₁, h₂⟩ hcontra
      exact hcontra ((ihφ hbox.1 p).mp h₁) ((ihψ hbox.2 p).mp h₂)
    · intro h
      constructor
      · by_contra hφ
        exact h (fun hφ' _ => hφ ((ihφ hbox.1 p).mpr hφ'))
      · by_contra hψ
        exact h (fun _ hψ' => hψ ((ihψ hbox.2 p).mpr hψ'))
  | or φ ψ ihφ ihψ =>
    simp only [sem, translateForward, Formula.Kripke.Satisfies]
    constructor
    · intro h hnφ
      cases h with
      | inl hφ => exact absurd ((ihφ hbox.1 p).mp hφ) hnφ
      | inr hψ => exact (ihψ hbox.2 p).mp hψ
    · intro h
      by_cases hφ : sem R I φ p
      · exact Or.inl hφ
      · exact Or.inr ((ihψ hbox.2 p).mpr (h (fun hφ' => hφ ((ihφ hbox.1 p).mpr hφ'))))
  | box φ ih =>
    -- OSLF: ∀ q, R q p → φ q; Foundation on converse: ∀ y, (Rᵒᵖ) p y → φ y
    -- where (Rᵒᵖ) p y = R y p, so both say ∀ q, R q p → φ q
    simp only [sem, translateForward, Formula.Kripke.Satisfies,
               oslfConverseModel, oslfConverseFrame, Frame.Rel']
    exact ⟨fun h q hRqp => (ih hbox q).mp (h q hRqp),
           fun h q hRqp => (ih hbox q).mpr (h q hRqp)⟩
  | dia _ => exact absurd hbox (by simp [boxOnly])

/-- **Modal-free correspondence**: modal-free formulas work on both frames. -/
theorem sem_iff_satisfies_modalFree (enc : AtomEncoding)
    (R : Pattern → Pattern → Prop) (I : AtomSem)
    {φ : OSLFFormula} (hmf : modalFree φ) (p : Pattern) :
    sem R I φ p ↔
    Formula.Kripke.Satisfies (oslfForwardModel R I enc) p (translateForward enc φ) :=
  sem_iff_satisfies_forward enc R I (modalFree_diaOnly hmf) p

/-! ## Frame Condition Consequences -/

/-- Reflexive R → forward frame validates axiom T (□φ → φ). -/
theorem forward_validates_T (R : Pattern → Pattern → Prop) (hRefl : ∀ p, R p p) :
    (oslfForwardFrame R) ⊧ Axioms.T (Formula.atom 0) := by
  have : (oslfForwardFrame R).IsReflexive := ⟨fun p => hRefl p⟩
  exact validate_AxiomT_of_reflexive

/-- Transitive R → forward frame validates axiom Four (□φ → □□φ). -/
theorem forward_validates_Four (R : Pattern → Pattern → Prop)
    (hTrans : ∀ p q r, R p q → R q r → R p r) :
    (oslfForwardFrame R) ⊧ Axioms.Four (Formula.atom 0) := by
  have : (oslfForwardFrame R).IsTransitive := ⟨fun _ _ _ => hTrans _ _ _⟩
  exact validate_AxiomFour_of_transitive

/-- Reflexive R → converse frame validates axiom T. -/
theorem converse_validates_T (R : Pattern → Pattern → Prop) (hRefl : ∀ p, R p p) :
    (oslfConverseFrame R) ⊧ Axioms.T (Formula.atom 0) := by
  have : (oslfConverseFrame R).IsReflexive := ⟨fun p => hRefl p⟩
  exact validate_AxiomT_of_reflexive

/-- Transitive R → converse frame validates axiom Four. -/
theorem converse_validates_Four (R : Pattern → Pattern → Prop)
    (hTrans : ∀ p q r, R p q → R q r → R p r) :
    (oslfConverseFrame R) ⊧ Axioms.Four (Formula.atom 0) := by
  have : (oslfConverseFrame R).IsTransitive :=
    ⟨fun _ _ _ hab hbc => hTrans _ _ _ hbc hab⟩
  exact validate_AxiomFour_of_transitive

/-- Symmetric R → forward frame validates axiom B (φ → □◇φ). -/
theorem forward_validates_B (R : Pattern → Pattern → Prop)
    (hSymm : ∀ p q, R p q → R q p) :
    (oslfForwardFrame R) ⊧ Axioms.B (Formula.atom 0) := by
  have : (oslfForwardFrame R).IsSymmetric := ⟨fun _ _ => hSymm _ _⟩
  exact validate_AxiomB_of_symmetric

/-! ## ValidOnModel Lifting -/

/-- If all patterns satisfy a diaOnly formula, the forward model validates it. -/
theorem validOnModel_forward (enc : AtomEncoding)
    (R : Pattern → Pattern → Prop) (I : AtomSem)
    {φ : OSLFFormula} (hdia : diaOnly φ)
    (hAll : ∀ p, sem R I φ p) :
    (oslfForwardModel R I enc) ⊧ translateForward enc φ :=
  fun p => (sem_iff_satisfies_forward enc R I hdia p).mp (hAll p)

/-- If all patterns satisfy a boxOnly formula, the converse model validates it. -/
theorem validOnModel_converse (enc : AtomEncoding)
    (R : Pattern → Pattern → Prop) (I : AtomSem)
    {φ : OSLFFormula} (hbox : boxOnly φ)
    (hAll : ∀ p, sem R I φ p) :
    (oslfConverseModel R I enc) ⊧ translateForward enc φ :=
  fun p => (sem_iff_satisfies_converse enc R I hbox p).mp (hAll p)

/-! ## Antitone Box -/

/-- Modal-free formulas have R-independent semantics. -/
private theorem sem_modalFree_irrel' {R₁ R₂ : Pattern → Pattern → Prop}
    (I : AtomSem) {φ : OSLFFormula} (hmf : modalFree φ)
    {p : Pattern} : sem R₁ I φ p ↔ sem R₂ I φ p := by
  induction φ generalizing p with
  | top | bot | atom _ => simp [sem]
  | and _ _ ih₁ ih₂ =>
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨(ih₁ hmf.1).mp h₁, (ih₂ hmf.2).mp h₂⟩,
           fun ⟨h₁, h₂⟩ => ⟨(ih₁ hmf.1).mpr h₁, (ih₂ hmf.2).mpr h₂⟩⟩
  | or _ _ ih₁ ih₂ =>
    exact ⟨fun h => h.elim (Or.inl ∘ (ih₁ hmf.1).mp) (Or.inr ∘ (ih₂ hmf.2).mp),
           fun h => h.elim (Or.inl ∘ (ih₁ hmf.1).mpr) (Or.inr ∘ (ih₂ hmf.2).mpr)⟩
  | imp _ _ ih₁ ih₂ =>
    exact ⟨fun h hφ => (ih₂ hmf.2).mp (h ((ih₁ hmf.1).mpr hφ)),
           fun h hφ => (ih₂ hmf.2).mpr (h ((ih₁ hmf.1).mp hφ))⟩
  | dia _ => exact absurd hmf (by simp [modalFree])
  | box _ => exact absurd hmf (by simp [modalFree])

/-- Anti-monotonicity of OSLF box under relation inclusion for modal-free subformulas.
Shrinking R preserves box satisfaction since fewer predecessors are quantified over. -/
theorem sem_antitone_box_via_bridge
    {R₁ R₂ : Pattern → Pattern → Prop}
    (hR : ∀ p q, R₂ p q → R₁ p q)
    (I : AtomSem) {φ : OSLFFormula} (hmf : modalFree φ)
    {p : Pattern} (h : sem R₁ I (.box φ) p) : sem R₂ I (.box φ) p := by
  intro q hR₂qp
  exact (sem_modalFree_irrel' I hmf).mp (h q (hR q p hR₂qp))

end Mettapedia.Logic.OSLFKripkeBridge
