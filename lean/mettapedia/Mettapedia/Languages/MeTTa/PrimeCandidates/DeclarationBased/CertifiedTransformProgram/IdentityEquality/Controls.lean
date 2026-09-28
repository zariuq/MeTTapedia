import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Metatheory
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Translation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.EtaConversion

/-!
# Controls for the identity profile

The identity profile reads equations as identity types.  It does not reflect
them:

* identity evidence between two variables does not make them convertible;
* reflexivity is still not evidence for `eqAt k` at an open index;
* the declared reflexivity assumption is a family of proofs, not identity
  evidence;
* the reflexivity realization at `zero` proves `Id num zero zero` and not
  `Id num zero (suc zero)`;
* reflexivity at a variable function `h` is not evidence for
  `Id (num → num) h (λ e. h e)`: the profile's conversion has no eta rule, so
  the source's eta principle is not realized by reflexivity.

What does inhabit `eqAt k` at an open index is the translated source proof
(`Translation.linkedZeroAdd_open`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open Presentation.ConstructorSystem (instanceOf Normal)
open SetProfile (numTy holdsName zeroNative sucNative addNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Confluence
open CertifiedTransformProgram.Preservation CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Metatheory
open CertifiedTransformProgram.IdentityEquality.Realizations
open CertifiedTransformProgram.Execution (numeral)
open Mettapedia.Logic

/-! ## Terms without computation steps in the profile -/

/-- A term that no equation of the profile matches has no root step. -/
theorem no_root {n : Nat} {term target : Tower.Tm n}
    (step : identityLinearRules.computation.step term target)
    (natives : SetProfile.nativeEquations.all
      (fun equation => !instanceOf equation.2.1 term) = true)
    (package : linearEquations.all (fun equation => !instanceOf equation.2.1 term) = true)
    (implication : instanceOf implicationLeft term = false)
    (universal : ∀ type, instanceOf (universalLeft type) term = false)
    (equation : ∀ type, instanceOf (equationLeft type) term = false) : False := by
  obtain ⟨m, left, right, rule, meets⟩ := identityConstructors.root_instance step
  cases rule with
  | equation type => rw [equation type] at meets; cases meets
  | linear rule =>
      cases rule with
      | implication => rw [implication] at meets; cases meets
      | universal type => rw [universal type] at meets; cases meets
      | native listed =>
          have excluded : (!instanceOf left term) = true := List.all_eq_true.mp natives _ listed
          rw [meets] at excluded
          cases excluded
      | package listed =>
          have excluded : (!instanceOf left term) = true := List.all_eq_true.mp package _ listed
          rw [meets] at excluded
          cases excluded

theorem numeral_normal {n : Nat} :
    ∀ count : Nat, Normal identityLinearRules (numeral count : Tower.Tm n)
  | 0 => Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl))
  | count + 1 =>
      Normal.app (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl)))
        (numeral_normal count) (fun _ equal => by cases equal)
        (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl))

theorem addZeroVar_normal {n : Nat} (index : Fin n) :
    Normal identityLinearRules (addNative zeroNative (.var index) : Tower.Tm n) :=
  Normal.app
    (Normal.app (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl)))
      (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl)))
      (fun _ equal => by cases equal)
      (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl)))
    (identityConstructors.normal_var index) (fun _ equal => by cases equal)
    (fun step => no_root step rfl rfl rfl (fun _ => rfl) (fun _ => rfl))

theorem toProfile_conversion {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv linearRules.headEq left right linearRules.computation) :
    Conv identityLinearRules.headEq left right identityLinearRules.computation := by
  simpa only [Tm.mapHead_id] using
    conversion.mapHead (fun head => head) linearToIdentity.headEq linearToIdentity.computation

/-! ## Not equality reflection -/

/-- The context `a b : num, e : Id num a b`. -/
abbrev pathContext : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil numT) numT) (.id numT (.var 1) (.var 0))

/-- Identity evidence between two variables is typed, and the variables are
not convertible: decoding equations is not equality reflection. -/
theorem not_reflection :
    Typing identityLinearRules pathContext (.var 0) (.id numT (.var 2) (.var 1)) ∧
      ¬ Conv identityLinearRules.headEq (.var 2 : Tower.Tm 3) (.var 1)
        identityLinearRules.computation := by
  refine ⟨Typing.var 0, fun conversion => ?_⟩
  have same := identityConstructors.eq_of_normal (identityConstructors.normal_var 2)
    (identityConstructors.normal_var 1) conversion
  cases same

/-! ## Reflexivity at an open index -/

/-- Reflexivity is still not evidence for `eqAt k` at the open index. -/
theorem refl_not_eqAt_open :
    ¬ Typing identityLinearRules (.snoc .nil numT) (.refl (.var 0)) (eqAtApp (.var 0)) := by
  intro typed
  obtain ⟨_, _, adjustment⟩ := CertifiedTransforms.reflGeneration typed
  have unfolded := toProfile_conversion (CertifiedTransformProgram.Controls.eqAt_converts (n := 1) (.var 0))
  have conversion := adjustment.toConvOfTargetDisjointHeads
    (fun _ toHead => identityConstructors.identity_not_head (.trans _ _ _ (.symm _ _ unfolded) toHead))
  obtain ⟨_, toPoint, _⟩ := identityConstructors.identity_components (.trans _ _ _ conversion unfolded)
  have same := identityConstructors.eq_of_normal (identityConstructors.normal_var 0)
    (addZeroVar_normal 0) toPoint
  cases same

/-! ## Wrong index -/

/-- The reflexivity realization at zero is not evidence that zero is one. -/
theorem reflRealization_wrong_index {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation identityLinearRules Γ) :
    ¬ Typing identityLinearRules Γ (.app (liftClosed reflRealization) zeroNative)
      (.id numT zeroNative (numeral 1)) := by
  intro typed
  have reduct := (step_preserves ⟨formed, typed⟩ (.betaPi _ _)).typing
  obtain ⟨toPoint, toEndpoint⟩ := identityHost.refl_endpoints reduct
  have same := identityConstructors.eq_of_normal (numeral_normal 0) (numeral_normal 1)
    (.trans _ _ _ (.symm _ _ toPoint) toEndpoint)
  cases same

/-! ## The declared assumption -/

/-- The declared reflexivity assumption is a family of proofs, not identity
evidence: its declared type reads as a dependent function. -/
theorem reflAssumption_not_identity {n : Nat} {Γ : Tower.Ctx n}
    (carrier point endpoint : Tower.Tm n) :
    ¬ Typing identityLinearRules Γ (.const SetProfile.reflName) (.id carrier point endpoint) := by
  intro typed
  have lookup : identityLinearRules.constantType SetProfile.reflName =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName SetProfile.reflCode) := by
    simpa only [Tm.mapHead_id] using
      linearToIdentity.constantType CertifiedTransformProgram.Controls.reflLookup
  have conversion := (typed.constantAdjustment lookup).toConvOfTargetDisjointHeads
    (fun _ toHead => identityConstructors.identity_not_head toHead)
  have decoded := toProfile_conversion (CertifiedTransformProgram.Controls.reflDecoded (n := n))
  obtain ⟨_, first, second⟩ :=
    identityConstructors.churchRosser (.trans _ _ _ (.symm _ _ decoded) conversion)
  obtain ⟨_, _, piShape⟩ := identityConstructors.stepStar_pi first
  obtain ⟨_, _, _, identityShape, _⟩ := identityConstructors.stepStar_identity second
  rw [piShape] at identityShape
  cases identityShape

/-! ## Eta -/

/-- Reflexivity at a variable function is not evidence that it equals its eta
expansion. -/
theorem eta_not_typed :
    ¬ Typing identityLinearRules (.snoc .nil (.pi numT numT)) (.refl (.var 0))
      (.id (.pi numT numT) (.var 0) EtaConversion.expansion) :=
  EtaConversion.eta_not_typed identityHost identityConstructors

#print axioms not_reflection
#print axioms eta_not_typed
#print axioms reflAssumption_not_identity
#print axioms refl_not_eqAt_open
#print axioms reflRealization_wrong_index

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Controls
