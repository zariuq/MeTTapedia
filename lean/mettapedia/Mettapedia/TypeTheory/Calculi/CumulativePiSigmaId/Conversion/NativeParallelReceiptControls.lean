import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallelSubstitution

/-!
# Native parallel replay with converted metadata and binding

The relational cons example develops a branch and a payload while replaying
five non-reflexive metadata certificates. The open nil example is instantiated
with a reducing argument, then exercised beneath a binder. Changed witnesses,
wrong results and captured variables fail the same authored checker.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt.Controls

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate
open NativeCompletedRootCertificate.Controls
open NativeRelatorConversionParallel.BindingExamples

def beta {n : Nat} (term : Tower.Tm n) : Tower.Tm n := .app (.lam (.var 0)) term

def betaReceipt {n : Nat} (term : Tower.Tm n) : Receipt (beta term) term :=
  .betaPi (.var 0) (Receipt.reflexive term)

def mixedCons : Tower.Tm 12 :=
  IntrinsicRelator.eliminateApp (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (beta (.var 6))
    (beta (Intrinsic.consApp (.var 11) (beta (.var 5)) (.var 3)))
    (beta (Intrinsic.consApp (.var 10) (.var 4) (.var 2)))
    (IntrinsicRelator.consRelApp (beta (.var 11)) (beta (.var 10)) (beta (.var 9))
      (beta (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

def mixedConsReceipt : Receipt mixedCons IntrinsicRelator.consIotaRight :=
  .relCons (identityBeta _) (identityBeta _) (identityBeta _) (identityBeta _) (identityBeta _)
    (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (betaReceipt (.var 6))
    (Receipt.reflexive _) (Receipt.reflexive _)
    (betaReceipt (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem mixed_cons_rechecks :
    NativeRelatorConversionChecking.check mixedConsReceipt.toCertificate.code
      mixedCons IntrinsicRelator.consIotaRight = true := mixedConsReceipt.toCertificate.checked

def wrongConsResult : Tower.Tm 12 :=
  .app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 3))
    (.var 2)) (.var 0)) (.var 0))
    (IntrinsicRelator.eliminateApp (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
      (.var 3) (.var 2) (.var 0))

theorem changed_relational_witness_rejected :
    NativeRelatorConversionChecking.check mixedConsReceipt.toCertificate.code
      mixedCons wrongConsResult = false := by decide +kernel

def openNilReceipt : Receipt openRelNil (.var 0) :=
  .relNil (identityBeta _) (.refl _) (.refl _) (.refl _) (.refl _)
    (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _)
    (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _)

def instantiatedNil : Receipt (inst0 (betaGround : Tower.Tm 0) openRelNil) ground :=
  instantiateReceipt (betaReceipt ground) openNilReceipt

theorem instantiated_nil_rechecks :
    NativeRelatorConversionChecking.check instantiatedNil.toCertificate.code
      (inst0 (betaGround : Tower.Tm 0) openRelNil) ground = true :=
  instantiatedNil.toCertificate.checked

def beneathBinder : Receipt (.lam (rename wk openRelNil) : Tower.Tm 1) (.lam (.var 1)) :=
  .lam (renameReceipt wk openNilReceipt)

def sourceSub : Sub Tower.Head 1 2 := fun _ => beta (.var 1)
def targetSub : Sub Tower.Head 1 2 := fun _ => .var 1

def substitutedBinder :
    Receipt (subst sourceSub (.lam (rename wk openRelNil))) (.lam (.var 2)) :=
  substituteReceipt (sourceSub := sourceSub) (targetSub := targetSub)
    (fun _ => betaReceipt (.var 1)) beneathBinder

theorem binder_rechecks :
    NativeRelatorConversionChecking.check substitutedBinder.toCertificate.code
      (subst sourceSub (.lam (rename wk openRelNil))) (.lam (.var 2)) = true :=
  substitutedBinder.toCertificate.checked

theorem captured_variable_rejected :
    NativeRelatorConversionChecking.check substitutedBinder.toCertificate.code
      (subst sourceSub (.lam (rename wk openRelNil))) (.lam (.var 1)) = false := by decide +kernel

def alternativeNil : Receipt openRelNil (.var 0) :=
  .relNil ((identityBeta _).trans (.refl _)) (.refl _) (.refl _) (.refl _) (.refl _)
    (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _)
    (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _) (Receipt.reflexive _)

theorem alternative_guard_rechecks :
    NativeRelatorConversionChecking.check alternativeNil.toCertificate.code openRelNil (.var 0) = true :=
  alternativeNil.toCertificate.checked

theorem distinct_guard_codes_retained :
    openNilReceipt.toCertificate.code ≠ alternativeNil.toCertificate.code := by
  intro equal
  have different : sizeOf openNilReceipt.toCertificate.code ≠
      sizeOf alternativeNil.toCertificate.code := by decide +kernel
  exact different (congrArg sizeOf equal)

/-- Contract beta before the body, or develop the native body and argument
first. Both paths are instantiated below with checked finite evidence. -/
def criticalSource : Tower.Tm 0 := .app (.lam openRelNil) betaGround

def outerFirst : Receipt criticalSource (inst0 betaGround openRelNil) :=
  .betaPi (Receipt.reflexive _) (Receipt.reflexive _)

def innerFirst : Receipt criticalSource (.app (.lam (.var 0)) ground) :=
  .app (.lam openNilReceipt) (betaReceipt ground)

theorem native_beta_square_rechecks :
    NativeRelatorConversionChecking.check outerFirst.toCertificate.code
        criticalSource (inst0 betaGround openRelNil) = true ∧
    NativeRelatorConversionChecking.check instantiatedNil.toCertificate.code
        (inst0 betaGround openRelNil) ground = true ∧
    NativeRelatorConversionChecking.check innerFirst.toCertificate.code
        criticalSource (.app (.lam (.var 0)) ground) = true ∧
    NativeRelatorConversionChecking.check (betaReceipt (ground : Tower.Tm 0)).toCertificate.code
        (.app (.lam (.var 0)) ground) ground = true :=
  ⟨outerFirst.toCertificate.checked, instantiatedNil.toCertificate.checked,
    innerFirst.toCertificate.checked, (betaReceipt ground).toCertificate.checked⟩

theorem undeveloped_endpoint_rejected :
    NativeRelatorConversionChecking.check instantiatedNil.toCertificate.code
      (inst0 (betaGround : Tower.Tm 0) openRelNil) betaGround = false := by decide +kernel

def unusedMotiveSource : Tower.Tm 4 :=
  Intrinsic.eliminateApp (.var 3) (beta (.var 2)) (.var 1) (.var 0)
    (Intrinsic.nilApp (.var 3))

def unchangedMotive : Receipt unusedMotiveSource (.var 1) :=
  .listNil (.refl _) (.var 3) (Receipt.reflexive _) (.var 1) (.var 0)

def developedMotive : Receipt unusedMotiveSource (.var 1) :=
  .listNil (.refl _) (.var 3) (betaReceipt (.var 2)) (.var 1) (.var 0)

theorem unused_development_is_retained : unchangedMotive ≠ developedMotive := by
  intro same
  cases same

/-- The authored conversion observation need not record development of an
argument discarded by the contraction. It is not a faithful receipt encoding. -/
theorem unused_development_erased_by_conversion :
    unchangedMotive.toCertificate.code = developedMotive.toCertificate.code := rfl

#print axioms mixed_cons_rechecks
#print axioms changed_relational_witness_rejected
#print axioms instantiated_nil_rechecks
#print axioms binder_rechecks
#print axioms captured_variable_rejected
#print axioms alternative_guard_rechecks
#print axioms distinct_guard_codes_retained
#print axioms native_beta_square_rechecks
#print axioms undeveloped_endpoint_rejected
#print axioms unused_development_is_retained
#print axioms unused_development_erased_by_conversion

#eval (NativeRelatorConversionChecking.check mixedConsReceipt.toCertificate.code
    mixedCons IntrinsicRelator.consIotaRight,
  NativeRelatorConversionChecking.check instantiatedNil.toCertificate.code
    (inst0 (betaGround : Tower.Tm 0) openRelNil) ground,
  NativeRelatorConversionChecking.check substitutedBinder.toCertificate.code
    (subst sourceSub (.lam (rename wk openRelNil))) (.lam (.var 2)))

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt.Controls
