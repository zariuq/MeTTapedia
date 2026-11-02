import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedMethods
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverses

/-!
# Original-program readback and caller transport for annotated Vector All

Erasure recovers the existing universe-parameterized raw program, and its
parameter-zero instance is the original annotated All program. Caller
substitution transports the actual binder annotations. None of these laws
asserts a predicate reading or reflection from raw typing to annotation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies

theorem universeMotive_substitute {n m : Nat} (result : LevelExpr Nat) (A : CTm Tower.Head n)
    (images : CSub Tower.Head n m) :
    (universeMotive result A).subst images = universeMotive result (A.subst images) := by
  simp only [universeMotive, motiveInner_substitute, CTm.subst, CTm.subst_liftSub_wk, CTm.liftSub, Fin.cases_zero]

theorem consCase_substitute {n m : Nat} (result : LevelExpr Nat) (A predicate : CTm Tower.Head n)
    (images : CSub Tower.Head n m) :
    (consCase result A predicate).subst images = consCase result (A.subst images) (predicate.subst images) := by
  simp only [consCase, vector, resultSort, weaken2, weaken4, CTm.subst, CTm.subst_liftSub_wk, CTm.liftSub]
  rfl

theorem allType_substitute {n m : Nat} (result : LevelExpr Nat) (A predicate length value : CTm Tower.Head n)
    (images : CSub Tower.Head n m) :
    (allType result A predicate length value).subst images =
      allType result (A.subst images) (predicate.subst images) (length.subst images) (value.subst images) := by
  simp only [allType, Programs.Annotated.Append.eliminate, unitType, CTm.subst,
    universeMotive_substitute, consCase_substitute]

theorem allType_erase {n : Nat} (result : LevelExpr Nat) (A predicate length value : CTm Tower.Head n) :
    (allType result A predicate length value).erase =
      NativeVectorAll.Universes.Canonical.allTypeAtUniverse result A.erase predicate.erase length.erase value.erase := by
  rw [NativeVectorAll.Universes.Canonical.allTypeAtUniverse_eq_eliminate]
  simp only [allType, Programs.Annotated.Append.eliminate, universeMotive, motiveInner, resultSort,
    consCase, unitType, vector, CTm.erase, CTm.erase_rename, NativeVectorAll.unitType,
    NativeVectorAll.allTypeConsCase, NativeVectorAll.weaken4, vecEliminateApp, sortTm, natTm, zeroTm,
    weaken2, weaken4, Presentation.rename_comp]
  rfl

theorem original_allType_typed (element : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    {n : Nat} {ambient : CCtx Tower.Head n} {A predicate length value : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element (.param 0) enabled) ambient A (Profile.elementSort element))
    (predicateTyped : CTyped (Profile.church element (.param 0) enabled) ambient predicate (.pi A (resultSort (.param 0))))
    (lengthTyped : CTyped (Profile.church element (.param 0) enabled) ambient length (.const natName))
    (valueTyped : CTyped (Profile.church element (.param 0) enabled) ambient value (vector A length)) :
    CTyped (Profile.church element (.param 0) enabled) ambient (Annotated.allType A predicate length value)
      (resultSort (.param 0)) := by
  rw [← original_all]
  exact allType_typed element (.param 0) enabled elementTyped predicateTyped lengthTyped valueTyped

theorem allType_caller (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    {n m : Nat} {ambient : CCtx Tower.Head n} {target : CCtx Tower.Head m}
    {A predicate length value : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (predicateTyped : CTyped (Profile.church element result enabled) ambient predicate (.pi A (resultSort result)))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName))
    (valueTyped : CTyped (Profile.church element result enabled) ambient value (vector A length))
    (images : CSub Tower.Head n m) (typed : CSubstMor (Profile.church element result enabled) ambient target images) :
    CTyped (Profile.church element result enabled) target
      (allType result (A.subst images) (predicate.subst images) (length.subst images) (value.subst images))
      (resultSort result) := by
  have transported := (allType_typed element result enabled elementTyped predicateTyped lengthTyped valueTyped).substitute typed
  simpa only [allType_substitute, resultSort, CTm.subst] using transported

#print axioms allType_erase
#print axioms original_allType_typed
#print axioms allType_caller

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation
