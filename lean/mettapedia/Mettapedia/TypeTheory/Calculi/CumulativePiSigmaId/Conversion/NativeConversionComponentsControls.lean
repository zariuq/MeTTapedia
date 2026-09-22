import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionComponents

/-!
# Computation and rejection controls for native conversion decomposition

The function and pair certificates deliberately pass through a List eliminator,
not just through function and pair constructors. Both components change, and
the codomain refers to both its bound variable and the outer context. These
are tests of conversion on scoped syntax, not typing-admission claims.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt.ComponentControls

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate

def listRoot {n : Nat} (parameter result : Tower.Tm n) :
    Certificate (Intrinsic.eliminateApp parameter parameter result parameter
      (Intrinsic.nilApp parameter)) result :=
  ⟨.single (.root (.indexed (.nil parameter parameter result parameter))), decide_eq_true rfl⟩

def listDetour {n : Nat} {left right : Tower.Tm n}
    (parameter : Tower.Tm n) (certificate : Certificate left right) :
    Certificate left right :=
  (listRoot parameter left).symm |>.trans
      ((listElim (.refl _) (.refl _) certificate (.refl _) (.refl _)).trans
        (listRoot parameter right))

def domain : Tower.Tm 1 := .var 0
def codomain : Tower.Tm 2 := .id (.var 1) (.var 0) (.var 0)
def sourceDomain : Tower.Tm 1 := .app (.lam (.var 0)) domain
def sourceCodomain : Tower.Tm 2 := .app (.lam (.var 0)) codomain

def piDetour : Certificate (.pi sourceDomain sourceCodomain) (.pi domain codomain) :=
  listDetour (.var 0) ((Controls.identityBeta domain).pi (Controls.identityBeta codomain))

def sigmaDetour : Certificate (.sigma sourceDomain sourceCodomain) (.sigma domain codomain) :=
  listDetour (.var 0) ((Controls.identityBeta domain).sigma (Controls.identityBeta codomain))

theorem pi_detour_has_four_steps : (certificatePath piDetour).length = 4 := rfl
theorem sigma_detour_has_four_steps : (certificatePath sigmaDetour).length = 4 := rfl

theorem pi_detour_computes_common :
    (joinCertificate piDetour).common = .pi domain codomain := rfl

theorem sigma_detour_computes_common :
    (joinCertificate sigmaDetour).common = .sigma domain codomain := rfl

def piComponentChecks : Bool :=
  let parts := piComponents piDetour
  NativeRelatorConversionChecking.check parts.1.code sourceDomain domain &&
    NativeRelatorConversionChecking.check parts.2.code sourceCodomain codomain

def sigmaComponentChecks : Bool :=
  let parts := sigmaComponents sigmaDetour
  NativeRelatorConversionChecking.check parts.1.code sourceDomain domain &&
    NativeRelatorConversionChecking.check parts.2.code sourceCodomain codomain

theorem pi_components_computed_and_checked : piComponentChecks = true := by decide +kernel
theorem sigma_components_computed_and_checked : sigmaComponentChecks = true := by decide +kernel

theorem pi_components_admitted :
    (checkedPiComponents piDetour.code sourceDomain domain sourceCodomain codomain).isSome = true :=
  (checkedPiComponents_domain _ _ _ _ _).trans piDetour.checked

theorem sigma_components_admitted :
    (checkedSigmaComponents sigmaDetour.code sourceDomain domain sourceCodomain codomain).isSome = true :=
  (checkedSigmaComponents_domain _ _ _ _ _).trans sigmaDetour.checked

/-- Replacing the outer type variable by the bound value is not an alignment. -/
theorem captured_codomain_rejected :
    (checkedPiComponents piDetour.code sourceDomain domain sourceCodomain
      (.id (.var 0) (.var 0) (.var 0))).isNone = true := by decide +kernel

theorem wrong_constructor_rejected :
    (checkedSigmaComponents piDetour.code sourceDomain domain sourceCodomain codomain).isNone = true := by
  decide +kernel

theorem projected_code_rejects_wrong_endpoint :
    NativeRelatorConversionChecking.check (piComponents piDetour).2.code sourceCodomain
      (.id (.var 0) (.var 0) (.var 0)) = false := by decide +kernel

def rootJoinChecks {n : Nat} (code : NativeRelatorRootConversionCode.Code n) : Bool :=
  match decoded : NativeRelatorRootConversionCode.decode code with
  | none => false
  | some (left, right) =>
      let certificate : Certificate left right :=
        ⟨.single (.root code), decide_eq_true decoded⟩
      let joined := joinCertificate certificate
      NativeRelatorConversionChecking.check (replayPath joined.fromLeft).code left joined.common &&
        NativeRelatorConversionChecking.check (replayPath joined.fromRight).code right joined.common

theorem all_five_root_joins_compute :
    rootJoinChecks NativeRelatorRootConversionCode.Examples.listNilCode = true ∧
    rootJoinChecks NativeRelatorRootConversionCode.Examples.listConsCode = true ∧
    rootJoinChecks NativeRelatorRootConversionCode.Examples.identityCode = true ∧
    rootJoinChecks NativeRelatorRootConversionCode.Examples.relNilCode = true ∧
    rootJoinChecks NativeRelatorRootConversionCode.Examples.relConsCode = true := by decide +kernel

theorem ingress_beneath_binder_keeps_step :
    (ingressPath NativeConversionPaths.Controls.relationalPath).length = 1 := rfl

theorem reversed_root_keeps_direction :
    Mettapedia.Logic.Relation.PathConfluence.directions (V := ReceiptGraph 12)
      (ingressPath NativeConversionPaths.Controls.reversedPath) = (0, 1) := rfl

theorem cancellation_keeps_both_directions :
    Mettapedia.Logic.Relation.PathConfluence.directions (V := ReceiptGraph 12)
      (ingressPath NativeConversionPaths.Controls.cancellationPath) = (1, 1) := rfl

theorem malformed_transitivity_rejected :
    (checkedJoin NativeRelatorConversionChecking.Examples.brokenJoin
      (.head NativeRelatorConversionChecking.Examples.firstHead)
      (.head NativeRelatorConversionChecking.Examples.secondHead)).isNone = true := by decide +kernel

#print axioms pi_detour_computes_common
#print axioms sigma_detour_computes_common
#print axioms pi_components_computed_and_checked
#print axioms sigma_components_computed_and_checked
#print axioms captured_codomain_rejected
#print axioms wrong_constructor_rejected
#print axioms projected_code_rejects_wrong_endpoint
#print axioms all_five_root_joins_compute
#print axioms cancellation_keeps_both_directions
#print axioms malformed_transitivity_rejected

#eval (piComponentChecks, sigmaComponentChecks,
  rootJoinChecks NativeRelatorRootConversionCode.Examples.relConsCode)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt.ComponentControls
