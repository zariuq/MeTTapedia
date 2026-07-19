/-
# Eta-long delivery boundary for the Pure beta root

Pure normal forms are already introduction-form at function type: executable
inference cannot accept a neutral head at a Pi result.  Consequently an
additional delivery-local eta expansion can only affect an ill-typed neutral;
it cannot repair a mismatch reached by an authenticated trace.  Non-Pi type
mismatches in `startSpine` also reject before `deliver` is called.
-/

import Mettapedia.GSLT.LanguageDef.Pure.BetaConversionBoundary

namespace Mettapedia.GSLT.LanguageDef.PureEtaDeliveryBoundary

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement
open Mettapedia.GSLT.LanguageDef.PureBeta
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement

/-- A syntactic Pi can never receive the beta root's atomic verdict. -/
theorem atomicityVerdict_pi_ne_atomic (fuel : Nat) (domain body : Expr) :
    atomicityVerdict fuel (.pi domain body) ≠ .atomic := by
  intro hatomic
  unfold atomicityVerdict at hatomic
  cases fuel with
  | zero =>
      simp [Mettapedia.GSLT.LanguageDef.PureBeta.normalize] at hatomic
  | succ fuel =>
      simp only [Mettapedia.GSLT.LanguageDef.PureBeta.normalize] at hatomic
      cases hdomain : Mettapedia.GSLT.LanguageDef.PureBeta.normalize fuel domain <;>
        cases hbody : Mettapedia.GSLT.LanguageDef.PureBeta.normalize fuel body <;>
          simp [hdomain, hbody, Expr.atomic] at hatomic

/-- Every executable Pi-typed Pure normal form is already a lambda. -/
theorem inferNf_pi_implies_lambda {context : Ctx} {term : Nf}
    {domain body : Expr}
    (hinfer :
      Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement.inferNf context term =
        .ok (.pi domain body)) :
    ∃ annotation lambdaBody, term = .lam annotation lambdaBody := by
  cases term with
  | lam annotation lambdaBody => exact ⟨annotation, lambdaBody, rfl⟩
  | head index arguments =>
      have htyped := inferNf_sound hinfer
      cases htyped with
      | head _ _ hatomic =>
          exact (atomicityVerdict_pi_ne_atomic normalizationFuel domain body hatomic).elim

/-- Thus a typed term reaching delivery at Pi type is already eta-long at its root. -/
def PiDeliveryIntroduction (context : Ctx) (term : Nf) (type : Expr) : Prop :=
  Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement.inferNf context term =
      .ok type →
    ∀ domain body, type = .pi domain body →
      ∃ annotation lambdaBody, term = .lam annotation lambdaBody

theorem typed_delivery_pi_introduction (context : Ctx) (term : Nf) (type : Expr) :
    PiDeliveryIntroduction context term type := by
  unfold PiDeliveryIntroduction
  intro hinfer domain body htype
  subst type
  exact inferNf_pi_implies_lambda hinfer

/-- A computed non-Pi mismatch rejects before any delivery continuation runs. -/
theorem startSpine_nonPi_mismatch_rejects
    {context : Ctx} {expected headType : Expr} {frames : List Frame}
    {head : Nat} {arguments : List Nf}
    (hnonPi : ∀ domain body, headType ≠ .pi domain body)
    (hmismatch :
      conversionVerdict normalizationFuel headType expected = .normalFormsDiffer) :
    Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement.startSpine
      context expected frames head arguments headType = .rejected := by
  cases headType with
  | pi domain body => exact (hnonPi domain body rfl).elim
  | sort => simp [PureBetaAtomicRefinement.startSpine, hmismatch]
  | bvar index => simp [PureBetaAtomicRefinement.startSpine, hmismatch]
  | lam domain body => simp [PureBetaAtomicRefinement.startSpine, hmismatch]
  | app fn argument => simp [PureBetaAtomicRefinement.startSpine, hmismatch]

/-! Positive and negative boundary fixtures. -/

def identityNf : Nf := .lam .sort (.head 0 [])

example :
    Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement.inferNf [] identityNf =
      .ok (.pi .sort .sort) := by decide

example : ∃ annotation body, identityNf = .lam annotation body :=
  @inferNf_pi_implies_lambda [] identityNf .sort .sort (by decide)

/-- A bare function head is rejected rather than smuggled through eta conversion. -/
example :
    Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement.inferNf
      [.pi .sort .sort] (.head 0 []) = .rejected := by decide

/-- A non-Pi mismatch remains rejected at the pre-delivery boundary. -/
example :
    Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement.startSpine
      [] .sort [] 0 [] (.bvar 0) = .rejected := by
  apply startSpine_nonPi_mismatch_rejects
  · intro domain body hpi
    cases hpi
  · decide

#print axioms atomicityVerdict_pi_ne_atomic
#print axioms inferNf_pi_implies_lambda
#print axioms typed_delivery_pi_introduction
#print axioms startSpine_nonPi_mismatch_rejects

end Mettapedia.GSLT.LanguageDef.PureEtaDeliveryBoundary
