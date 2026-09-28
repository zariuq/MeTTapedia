import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Coherence

/-!
# Controls for annotated terms and their erasure, at every rule package

Positive:

* erasure is surjective (`erase_onto`) and commutes with opening a binder, on an
  instance (`erase_inst0_instance`);
* an annotated β-step erases to a weak-head step and to a step of the directed
  reduction of every rule package (`beta_erases`);
* the erasure of an annotated derivation of the identity is a derivation of the
  unannotated identity (`identity_erases`).

Negative:

* erasure is not injective: the identity at two different domains has one
  erasure (`identity_not_injective`);
* a step inside a domain is no step after erasure (`domainStep_invisible`): the
  identity at `(λ (y : B). y) A` steps to the identity at `A`, with one erasure.

Controls of coherence, which need a concrete universe presentation, are in the
cumulative tower (`Instances.TowerAnnotated`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace Controls

open Normalization (WhStep)

variable {Head : Type} {R : Rules Head}

/-- The identity with domain `A`. -/
abbrev identity {n : Nat} (A : CTm Head n) : CTm Head n := .lam A (.var 0)

/-- Positive: every term is an erasure. -/
theorem erase_onto (domain : CTm Head 0) {n : Nat} (t : Tm Head n) :
    ∃ t' : CTm Head n, t'.erase = t :=
  ⟨CTm.annotateWith domain t, CTm.erase_annotateWith domain t⟩

/-- Positive: erasure commutes with opening a binder, on an instance. -/
theorem erase_inst0_instance (A : CTm Head 0) :
    (CTm.inst0 (identity A) (.app (.var 0) (.var 0))).erase =
      Presentation.inst0 (Tm.lam (.var 0)) (.app (.var 0) (.var 0)) :=
  rfl

/-- Positive: an annotated β-step erases to a weak-head step and to a step of
the directed reduction. -/
theorem beta_erases (roles : Normalization.Roles Head) {n : Nat} (A a : CTm Head n) :
    WhStep R roles (CTm.app (identity A) a).erase a.erase ∧
      StrongNormalization.Reduces R (CTm.app (identity A) a).erase a.erase :=
  ⟨(CWhStep.beta A (.var 0) a).erase_whStep, (CWhStep.beta A (.var 0) a).erase_reduces⟩

/-- Positive: the erasure of an annotated typing of the identity. -/
theorem identity_erases {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {u w : Head} (typeA : CTyped P Γ A (.head w)) (hw : R.isUniverse w)
    (typePi : CTyped P Γ (.pi A (A.rename wk)) (.head u)) (hu : R.isUniverse u) :
    Typed R Γ.erase (.lam (.var 0)) (.pi A.erase (Presentation.rename wk A.erase)) := by
  have := CDerivable.erase (CDerivable.lamIntro typeA hw typePi hu (.var 0) :
    CTyped P Γ (identity A) (.pi A (A.rename wk)))
  simpa [CStatement.erase, CTm.erase] using this

/-- Negative: two annotated terms with one erasure. -/
theorem identity_not_injective {n : Nat} {A A' : CTm Head n} (different : A ≠ A') :
    identity A ≠ identity A' ∧ (identity A).erase = (identity A').erase :=
  CTm.erase_not_injective different

/-- Negative: a step inside a domain changes the annotated term and not its
erasure. -/
theorem domainStep_invisible (root : CRootComputation Head) (headEq : Head → Head → Prop)
    {n : Nat} (A B : CTm Head n) :
    CStepCore root headEq (identity (.app (identity B) A)) (identity A) ∧
      (identity (.app (identity B) A)).erase = (identity A).erase :=
  ⟨.congLamDom (.betaPi B (.var 0) A), rfl⟩

end Controls
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
