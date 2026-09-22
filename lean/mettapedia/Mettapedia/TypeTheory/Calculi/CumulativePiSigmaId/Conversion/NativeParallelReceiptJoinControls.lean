import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptControls

/-!
# Executing native parallel diamonds and finite joins

These cases run the general join algorithm, not hand-authored joining paths.
They include converted metadata, simultaneous payload development, binding,
all five native roots, both projections, and two distinct reduction orders.
The output certificates are tested by the authored checker; altered endpoints
and relational witnesses are rejected.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt.JoinControls

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate
open NativeCompletedRootCertificate.Controls
open NativeParallelReceipt.Controls
open NativeRelatorConversionParallel.BindingExamples

def rechecks {n : Nat} {left right : Tower.Tm n} (joined : LocalJoin left right) : Bool :=
  NativeRelatorConversionChecking.check joined.fromLeft.toCertificate.code left joined.common &&
    NativeRelatorConversionChecking.check joined.fromRight.toCertificate.code right joined.common

theorem rechecks_true {n : Nat} {left right : Tower.Tm n} (joined : LocalJoin left right) :
    rechecks joined = true := by
  simp only [rechecks, Bool.and_eq_true]
  exact ⟨joined.fromLeft.toCertificate.checked, joined.fromRight.toCertificate.checked⟩

def betaNativeJoin := localJoin criticalSource outerFirst innerFirst

theorem beta_native_common : betaNativeJoin.common = (ground : Tower.Tm 0) := by rfl

def mixedConsStructural : Receipt mixedCons IntrinsicRelator.consIotaLeft :=
  .app (.relPrefixCong (.var 11) (.var 10) (.var 9) (.var 8) (.var 7)
      (betaReceipt (.var 6))
      (.betaPi (.var 0) (.consCong (.var 11) (betaReceipt (.var 5)) (.var 3)))
      (betaReceipt (Intrinsic.consApp (.var 10) (.var 4) (.var 2))))
    (.consRelCong (betaReceipt (.var 11)) (betaReceipt (.var 10)) (betaReceipt (.var 9))
      (betaReceipt (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

def relationalConsJoin := localJoin mixedCons mixedConsReceipt mixedConsStructural

theorem relational_cons_common : relationalConsJoin.common = IntrinsicRelator.consIotaRight := by rfl

def reversedRelationalConsJoin := localJoin mixedCons mixedConsStructural mixedConsReceipt

theorem reversed_relational_cons_common :
    reversedRelationalConsJoin.common = IntrinsicRelator.consIotaRight := by rfl

theorem changed_join_witness_rejected :
    NativeRelatorConversionChecking.check relationalConsJoin.fromRight.toCertificate.code
      IntrinsicRelator.consIotaLeft wrongConsResult = false := by decide +kernel

def underBinderJoin := localJoin (.lam mixedCons)
  (.lam mixedConsReceipt) (.lam mixedConsStructural)

theorem under_binder_common : underBinderJoin.common = .lam IntrinsicRelator.consIotaRight := by rfl

def listNilStructural :
    Receipt unusedMotiveSource
      (Intrinsic.eliminateApp (.var 3) (.var 2) (.var 1) (.var 0) (Intrinsic.nilApp (.var 3))) :=
  .app (.listPrefixCong (.var 3) (betaReceipt (.var 2)) (.var 1) (.var 0))
    (.nilCong (.var 3))

def listNilJoin := localJoin unusedMotiveSource unchangedMotive listNilStructural

theorem list_nil_common : listNilJoin.common = .var 1 := by rfl

def listConsSource : Tower.Tm 6 :=
  Intrinsic.eliminateApp (.var 5) (.var 4) (.var 3) (beta (.var 2))
    (Intrinsic.consApp (beta (.var 5)) (beta (.var 1)) (.var 0))

def listConsContract :
    Receipt listConsSource
      (.app (.app (.app (.var 2) (.var 1)) (.var 0))
        (Intrinsic.eliminateApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 0))) :=
  .listCons (identityBeta _) (.var 5) (.var 4) (.var 3) (betaReceipt (.var 2))
    (betaReceipt (.var 1)) (.var 0)

def listConsStructural :
    Receipt listConsSource
      (Intrinsic.eliminateApp (.var 5) (.var 4) (.var 3) (.var 2)
        (Intrinsic.consApp (.var 5) (.var 1) (.var 0))) :=
  .app (.listPrefixCong (.var 5) (.var 4) (.var 3) (betaReceipt (.var 2)))
    (.consCong (betaReceipt (.var 5)) (betaReceipt (.var 1)) (.var 0))

def listConsJoin := localJoin listConsSource listConsContract listConsStructural

theorem list_cons_common :
    listConsJoin.common =
      .app (.app (.app (.var 2) (.var 1)) (.var 0))
        (Intrinsic.eliminateApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 0)) := by rfl

def identitySource : Tower.Tm 4 :=
  Intrinsic.identityEliminateApp (.var 3) (.var 2) (.var 1) (beta (.var 0))
    (beta (.var 2)) (.refl (beta (.var 2)))

def identityContract : Receipt identitySource (.var 0) :=
  .identity (identityBeta _) (identityBeta _)
    (.var 3) (.var 2) (.var 1) (betaReceipt (.var 0))
    (Receipt.reflexive _) (Receipt.reflexive _)

def identityStructural :
    Receipt identitySource
      (Intrinsic.identityEliminateApp (.var 3) (.var 2) (.var 1) (.var 0)
        (.var 2) (.refl (.var 2))) :=
  .app (.identityPrefixCong (.var 3) (.var 2) (.var 1)
      (betaReceipt (.var 0)) (betaReceipt (.var 2)))
    (.refl (betaReceipt (.var 2)))

def identityJoin := localJoin identitySource identityContract identityStructural

theorem identity_common : identityJoin.common = .var 0 := by rfl

def relationalNilJoin := localJoin openRelNil openNilReceipt (Receipt.reflexive openRelNil)

theorem relational_nil_common : relationalNilJoin.common = .var 0 := by rfl

def capturedJoin := localJoin (subst sourceSub (.lam (rename wk openRelNil)))
  substitutedBinder (Receipt.reflexive _)

theorem capture_free_common : capturedJoin.common = .lam (.var 2) := by rfl

theorem captured_join_endpoint_rejected :
    NativeRelatorConversionChecking.check capturedJoin.fromRight.toCertificate.code
      (subst sourceSub (.lam (rename wk openRelNil))) (.lam (.var 1)) = false := by decide +kernel

def projectionFirst : Receipt (.fst (.pair (beta (.var 1)) (beta (.var 0))) : Tower.Tm 2)
    (beta (.var 1)) :=
  .betaSigmaFst (Receipt.reflexive _) (Receipt.reflexive _)

def projectionInner : Receipt (.fst (.pair (beta (.var 1)) (beta (.var 0))) : Tower.Tm 2)
    (.fst (.pair (.var 1) (.var 0))) :=
  .fst (.pair (betaReceipt (.var 1)) (betaReceipt (.var 0)))

def projectionJoin := localJoin _ projectionFirst projectionInner

theorem projection_common : projectionJoin.common = .var 1 := by rfl

def secondProjectionJoin := localJoin
  (.snd (.pair (beta (.var 1)) (beta (.var 0))) : Tower.Tm 2)
  (.betaSigmaSnd (Receipt.reflexive _) (Receipt.reflexive _))
  (.snd (.pair (betaReceipt (.var 1)) (betaReceipt (.var 0))))

theorem second_projection_common : secondProjectionJoin.common = .var 0 := by rfl

/-- Develop separate components in separate rounds. The finite join therefore
contains two continuation edges on each side, not just one local diamond. -/
def pairSource : Tower.Tm 2 := .pair (beta (.var 1)) (beta (.var 0))
def pairTarget : Tower.Tm 2 := .pair (.var 1) (.var 0)

def leftThenRight : DirectedPath pairSource pairTarget :=
  .cons (.cons .nil (.pair (betaReceipt (.var 1)) (Receipt.reflexive _)))
    (.pair (.var 1) (betaReceipt (.var 0)))

def rightThenLeft : DirectedPath pairSource pairTarget :=
  .cons (.cons .nil (.pair (Receipt.reflexive _) (betaReceipt (.var 0))))
    (.pair (betaReceipt (.var 1)) (.var 0))

def pairPathsJoin := joinPaths leftThenRight rightThenLeft

theorem paths_have_computed_endpoint : pairPathsJoin.common = pairTarget := by rfl

theorem paths_keep_two_continuations :
    pairPathsJoin.fromLeft.length = 2 ∧ pairPathsJoin.fromRight.length = 2 :=
  joinPaths_lengths leftThenRight rightThenLeft

theorem pair_paths_recheck :
    NativeRelatorConversionChecking.check (replayPath pairPathsJoin.fromLeft).code pairTarget pairTarget = true ∧
    NativeRelatorConversionChecking.check (replayPath pairPathsJoin.fromRight).code pairTarget pairTarget = true := by
  exact joinPaths_rechecks leftThenRight rightThenLeft


/-- Reverse the first edge, then follow the second. The algorithm must discover
the common endpoint, rather than merely replay either original path forward. -/
def betaNativeZigzag :
    SymmetricPath (inst0 betaGround openRelNil) (.app (.lam (.var 0)) (ground : Tower.Tm 0)) :=
  .cons (.cons .nil (.inr outerFirst)) (.inl innerFirst)

def betaNativeZigzagJoin := joinSymmetricPath betaNativeZigzag

theorem zigzag_common : betaNativeZigzagJoin.common = (ground : Tower.Tm 0) := by rfl

theorem zigzag_continuation_lengths :
    betaNativeZigzagJoin.fromLeft.length = 1 ∧ betaNativeZigzagJoin.fromRight.length = 1 :=
  joinSymmetricPath_lengths betaNativeZigzag

theorem zigzag_continuations_recheck :
    NativeRelatorConversionChecking.check
      (replayPath betaNativeZigzagJoin.fromLeft).code (inst0 betaGround openRelNil) ground = true ∧
    NativeRelatorConversionChecking.check
      (replayPath betaNativeZigzagJoin.fromRight).code (.app (.lam (.var 0)) ground) ground = true :=
  ⟨(replayPath betaNativeZigzagJoin.fromLeft).checked,
    (replayPath betaNativeZigzagJoin.fromRight).checked⟩

theorem undeveloped_zigzag_endpoint_rejected :
    NativeRelatorConversionChecking.check
      (replayPath betaNativeZigzagJoin.fromLeft).code (inst0 betaGround openRelNil) betaGround = false := by
  decide +kernel

/-- Original route distinctions survive the existence of a common endpoint. -/
theorem joining_does_not_identify_receipts : unchangedMotive ≠ developedMotive :=
  unused_development_is_retained

#print axioms beta_native_common
#print axioms relational_cons_common
#print axioms changed_join_witness_rejected
#print axioms under_binder_common
#print axioms list_nil_common
#print axioms list_cons_common
#print axioms identity_common
#print axioms relational_nil_common
#print axioms capture_free_common
#print axioms captured_join_endpoint_rejected
#print axioms projection_common
#print axioms second_projection_common
#print axioms paths_have_computed_endpoint
#print axioms paths_keep_two_continuations
#print axioms pair_paths_recheck
#print axioms zigzag_common
#print axioms zigzag_continuation_lengths
#print axioms zigzag_continuations_recheck
#print axioms undeveloped_zigzag_endpoint_rejected
#print axioms joining_does_not_identify_receipts

#eval [rechecks betaNativeJoin, rechecks relationalConsJoin, rechecks reversedRelationalConsJoin,
  rechecks underBinderJoin, rechecks listNilJoin, rechecks listConsJoin, rechecks identityJoin,
  rechecks relationalNilJoin, rechecks capturedJoin, rechecks projectionJoin, rechecks secondProjectionJoin]
#eval (pairPathsJoin.fromLeft.length, pairPathsJoin.fromRight.length,
  NativeRelatorConversionChecking.check (replayPath pairPathsJoin.fromLeft).code pairTarget pairTarget,
  NativeRelatorConversionChecking.check (replayPath pairPathsJoin.fromRight).code pairTarget pairTarget)

#eval (betaNativeZigzagJoin.fromLeft.length, betaNativeZigzagJoin.fromRight.length,
  NativeRelatorConversionChecking.check (replayPath betaNativeZigzagJoin.fromLeft).code
    (inst0 betaGround openRelNil) ground,
  NativeRelatorConversionChecking.check (replayPath betaNativeZigzagJoin.fromRight).code
    (.app (.lam (.var 0)) ground) ground)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt.JoinControls
