import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.Logic.HOL.Syntax.Subst
import Mettapedia.Logic.HOL.Soundness

/-!
# Native substitution and intrinsic HOL substitution

Partial erasure commutes with weakening and capture-avoiding term substitution.
The comparison uses the native operations directly, including the shift under
each binder. Unsupported HOL logical constructors still have no native erasure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

universe w

open MathdataKernel
open Mettapedia.Logic.HOL

variable {environment : Environment} {Γ Δ : Ctx Base} {τ σ : Ty Base}

private theorem lift_index_shift (ρ : Rename Base Γ Δ) (cutoff amount : Nat)
    (indexed : ∀ {a} (v : Var Γ a), variableIndex (ρ v) =
      if variableIndex v < cutoff then variableIndex v else variableIndex v + amount) :
    ∀ {a} (v : Var (σ :: Γ) a), variableIndex (Rename.lift ρ v) =
      if variableIndex v < cutoff + 1 then variableIndex v else variableIndex v + amount := by
  intro a v
  cases v with
  | vz => simp [Rename.lift, variableIndex]
  | vs v =>
      simp only [Rename.lift, variableIndex, indexed]
      split <;> split <;> omega

/-- Erasure respects any typed renaming implementing a native index shift. -/
theorem erase_rename_shift (term : Term (Constant environment) Γ τ)
    (ρ : Rename Base Γ Δ) (cutoff amount : Nat)
    (indexed : ∀ {a} (v : Var Γ a), variableIndex (ρ v) =
      if variableIndex v < cutoff then variableIndex v else variableIndex v + amount) :
    erase (rename ρ term) = (erase term).map (Tm.shift cutoff amount) := by
  induction term generalizing Δ cutoff with
  | var v =>
      simp only [rename, erase, Option.map_some, Tm.shift, indexed]
      split <;> rfl
  | const c => cases c <;> rfl
  | app f a ihf iha =>
      simp only [rename, erase, ihf ρ cutoff indexed, iha ρ cutoff indexed]
      cases erase f <;> cases erase a <;> rfl
  | imp f a ihf iha =>
      simp only [rename, erase, ihf ρ cutoff indexed, iha ρ cutoff indexed]
      cases erase f <;> cases erase a <;> rfl
  | lam body ih =>
      simp only [rename, erase, ih (Rename.lift ρ) (cutoff + 1)
        (lift_index_shift ρ cutoff amount indexed)]
      cases erase body <;> rfl
  | all body ih =>
      simp only [rename, erase, ih (Rename.lift ρ) (cutoff + 1)
        (lift_index_shift ρ cutoff amount indexed)]
      cases erase body <;> rfl
  | top | bot | and | or | not | eq | ex => rfl

theorem erase_weaken (term : Term (Constant environment) Γ τ) :
    erase (weaken (σ := σ) term) = (erase term).map (Tm.shift 0 1) := by
  apply erase_rename_shift
  intro a v
  simp [Rename.weaken, variableIndex]

/-- Two native shifts at the same cutoff add their amounts. -/
theorem native_shift_add (term : Tm) (cutoff first second : Nat) :
    Tm.shift cutoff first (Tm.shift cutoff second term) =
      Tm.shift cutoff (second + first) term := by
  induction term generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff
      · simp [Tm.shift, below]
      · simp [Tm.shift, below, show ¬ index + second < cutoff by omega, Nat.add_assoc]
  | named | prim => rfl
  | app f a ihf iha | imp f a ihf iha => simp [Tm.shift, ihf, iha]
  | lam a body ih | all a body ih => simp [Tm.shift, ih]
  | typeApp f a ih | typeLam f ih | typeAll f ih => simp [Tm.shift, ih]

theorem native_shift_zero (term : Tm) (cutoff : Nat) : Tm.shift cutoff 0 term = term := by
  induction term generalizing cutoff with
  | db index => simp [Tm.shift]
  | named | prim => rfl
  | app f a ihf iha | imp f a ihf iha => simp [Tm.shift, ihf, iha]
  | lam a body ih | all a body ih => simp [Tm.shift, ih]
  | typeApp f a ih | typeLam f ih | typeAll f ih => simp [Tm.shift, ih]

private theorem native_shift_instantiate_variable (replacement : Tm) (depth index : Nat) :
    Tm.shift 0 1 (Tm.instantiateAt depth replacement (.db index)) =
      Tm.instantiateAt (depth + 1) replacement (.db (index + 1)) := by
  simp only [Tm.instantiateAt]
  by_cases below : index < depth
  · simp [below, show index + 1 < depth + 1 by omega, Tm.shift]
  · by_cases same : index = depth
    · subst index
      simp [native_shift_add]
    · simp [below, same, show ¬ index + 1 < depth + 1 by omega, Tm.shift]
      omega

private theorem lift_erased_substitution (substitution : Subst (Constant environment) Γ Δ)
    (replacement : Tm) (depth : Nat)
    (erased : ∀ {a} (v : Var Γ a), erase (substitution v) =
      some (Tm.instantiateAt depth replacement (.db (variableIndex v)))) :
    ∀ {a} (v : Var (σ :: Γ) a), erase (Subst.lift substitution v) =
      some (Tm.instantiateAt (depth + 1) replacement (.db (variableIndex v))) := by
  intro a v
  cases v with
  | vz => simp [Subst.lift, erase, variableIndex, Tm.instantiateAt]
  | vs v =>
      change erase (weaken (substitution v)) = _
      rw [erase_weaken, erased, Option.map_some]
      exact congrArg some (native_shift_instantiate_variable replacement depth (variableIndex v))

/-- Erasure intertwines typed substitution with the native single-variable
operation whenever their actions on variables agree. -/
theorem erase_subst_instantiateAt (term : Term (Constant environment) Γ τ)
    (substitution : Subst (Constant environment) Γ Δ) (replacement : Tm) (depth : Nat)
    (erased : ∀ {a} (v : Var Γ a), erase (substitution v) =
      some (Tm.instantiateAt depth replacement (.db (variableIndex v)))) :
    erase (subst substitution term) =
      (erase term).map (Tm.instantiateAt depth replacement) := by
  induction term generalizing Δ depth with
  | var v => exact erased v
  | const c => cases c <;> rfl
  | app f a ihf iha =>
      simp only [subst, erase, ihf substitution depth erased, iha substitution depth erased]
      cases erase f <;> cases erase a <;> rfl
  | imp f a ihf iha =>
      simp only [subst, erase, ihf substitution depth erased, iha substitution depth erased]
      cases erase f <;> cases erase a <;> rfl
  | lam body ih =>
      simp only [subst, erase, ih (Subst.lift substitution) (depth + 1)
        (lift_erased_substitution substitution replacement depth erased)]
      cases erase body <;> rfl
  | all body ih =>
      simp only [subst, erase, ih (Subst.lift substitution) (depth + 1)
        (lift_erased_substitution substitution replacement depth erased)]
      cases erase body <;> rfl
  | top | bot | and | or | not | eq | ex => rfl

/-- Instantiating an intrinsic binder erases to Megalodon's own substitution. -/
theorem erase_instantiate (argument : Term (Constant environment) Γ σ)
    (body : Term (Constant environment) (σ :: Γ) τ) {raw : Tm}
    (erasedArgument : erase argument = some raw) :
    erase (instantiate argument body) = (erase body).map (Tm.instantiate raw) := by
  apply erase_subst_instantiateAt
  intro a v
  cases v with
  | vz => simpa [Subst.single, variableIndex, Tm.instantiateAt, native_shift_zero] using erasedArgument
  | vs v => simp [Subst.single, variableIndex, erase, Tm.instantiateAt]

/-- The native beta redex and its native contractum are erasures of intrinsic
terms with equal denotations in every Henkin model. This is a local beta law,
not a claim about native delta normalization or arbitrary proof acceptance. -/
theorem native_beta_interpretation (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (argument : Term (Constant environment) Γ σ)
    (body : Term (Constant environment) (σ :: Γ) τ)
    (valuation : HenkinModel.Valuation M Γ) {rawArgument rawBody : Tm}
    (erasedArgument : erase argument = some rawArgument)
    (erasedBody : erase body = some rawBody) :
    erase (.app (.lam body) argument) =
        some (.app (.lam (reifyType σ) rawBody) rawArgument) ∧
      erase (instantiate argument body) = some (Tm.instantiate rawArgument rawBody) ∧
      HenkinModel.denote M (.app (.lam body) argument) valuation =
        HenkinModel.denote M (instantiate argument body) valuation := by
  refine ⟨by simp [erase, erasedBody, erasedArgument], ?_, ?_⟩
  · rw [erase_instantiate argument body erasedArgument, erasedBody]
    rfl
  · exact (Soundness.denote_instantiate_term M argument body valuation).symm

private theorem plainAnnotations_shift (term : Tm) (depth cutoff amount : Nat) :
    plainAnnotations depth (Tm.shift cutoff amount term) = plainAnnotations depth term := by
  induction term generalizing cutoff with
  | db index => simp only [Tm.shift]; split <;> rfl
  | named | prim => rfl
  | app f a ihf iha | imp f a ihf iha => simp [Tm.shift, plainAnnotations, ihf, iha]
  | lam a body ih | all a body ih => simp [Tm.shift, plainAnnotations, ih]
  | typeApp | typeLam | typeAll => rfl

private theorem plainAnnotations_instantiateAt {term replacement : Tm} {depth : Nat}
    (termFormed : plainAnnotations depth term = true)
    (replacementFormed : plainAnnotations depth replacement = true) (cutoff : Nat) :
    plainAnnotations depth (Tm.instantiateAt cutoff replacement term) = true := by
  induction term generalizing cutoff with
  | db index =>
      simp only [Tm.instantiateAt]
      split
      · rfl
      · split
        · rw [plainAnnotations_shift, replacementFormed]
        · rfl
  | named | prim => rfl
  | app f a ihf iha | imp f a ihf iha =>
      simp only [plainAnnotations, Bool.and_eq_true] at termFormed
      simp [Tm.instantiateAt, plainAnnotations, ihf termFormed.1, iha termFormed.2]
  | lam a body ih | all a body ih =>
      simp only [plainAnnotations, Bool.and_eq_true] at termFormed
      simp [Tm.instantiateAt, plainAnnotations, termFormed.1, ih termFormed.2]
  | typeApp | typeLam | typeAll => simp [plainAnnotations] at termFormed

/-- Native typing is preserved by native substitution on the interpreted
fragment. Both arguments are raw native inference judgments; intrinsic typing
and exact erasure supply the proof between them. -/
theorem native_infer_instantiate {rawArgument rawBody : Tm} {depth : Nat}
    (argumentLookups : PlainLookups environment depth rawArgument)
    (bodyLookups : PlainLookups environment depth rawBody)
    (argumentFormed : plainAnnotations depth rawArgument = true)
    (bodyFormed : plainAnnotations depth rawBody = true)
    (argumentTyped : inferTerm environment depth (Γ.map reifyType) rawArgument =
      some (reifyType σ))
    (bodyTyped : inferTerm environment depth ((σ :: Γ).map reifyType) rawBody =
      some (reifyType τ)) :
    inferTerm environment depth (Γ.map reifyType) (Tm.instantiate rawArgument rawBody) =
      some (reifyType τ) := by
  obtain ⟨argument, erasedArgument⟩ :=
    (infer_iff_interpretation_of_plainLookups argumentLookups argumentFormed).1 argumentTyped
  obtain ⟨body, erasedBody⟩ :=
    (infer_iff_interpretation_of_plainLookups bodyLookups bodyFormed).1 bodyTyped
  apply infer_of_erase (instantiate argument body)
  · rw [erase_instantiate argument body erasedArgument, erasedBody]
    rfl
  · exact plainAnnotations_instantiateAt bodyFormed argumentFormed 0

namespace CaptureAvoidance

/-- The free argument is outside both the beta binder and the nested binder. -/
def argument : Term (Constant {}) [.prop] .prop := .var .vz

def body : Term (Constant {}) [.prop, .prop] (.arr .prop .prop) :=
  .lam (.var (.vs .vz))

theorem shifted_contractum :
    erase (instantiate argument body) = some (.lam .prop (.db 1)) := by
  rw [erase_instantiate argument body (raw := .db 0) rfl]
  rfl

/-- Leaving the inserted index at zero captures it by the nested binder. -/
theorem unshifted_contractum_rejected :
    erase (instantiate argument body) ≠ some (.lam .prop (.db 0)) := by
  rw [shifted_contractum]
  decide

end CaptureAvoidance

#print axioms erase_rename_shift
#print axioms erase_instantiate
#print axioms native_beta_interpretation
#print axioms native_infer_instantiate
#print axioms CaptureAvoidance.shifted_contractum
#print axioms CaptureAvoidance.unshifted_contractum_rejected

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
