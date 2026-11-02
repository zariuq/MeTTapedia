import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure

/-!
# Explicit binder annotations for the existing Vector All type program

The type-level motive binds a length and a vector. Its cons case binds
length, head, tail and the recursively computed type. Erasure recovers the
original program, and scoped substitution preserves every annotation.
Source typing still requires the selected type-level recursor profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies

def vector {n : Nat} (element length : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const vecName) element) length

def weaken2 {n : Nat} (term : CTm Tower.Head n) : CTm Tower.Head (n + 2) := (term.rename wk).rename wk
def weaken4 {n : Nat} (term : CTm Tower.Head n) : CTm Tower.Head (n + 4) := weaken2 (weaken2 term)

def universeMotive {n : Nat} (element : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam (.const natName) (.lam (vector (element.rename wk) (.var 0)) (.head (.sort motiveLevel)))

def consCase {n : Nat} (element predicate : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam (.const natName) (.lam (element.rename wk)
    (.lam (vector (weaken2 element) (.var 1))
      (.lam (.head (.sort motiveLevel)) (.sigma (.app (weaken4 predicate) (.var 2)) (.var 1)))))

def allType {n : Nat} (element predicate length value : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.app (.app (.app (.app (.const vecEliminateName) element) (universeMotive element))
    (.id (.const natName) (.const zeroName) (.const zeroName))) (consCase element predicate)) length) value

theorem erase_vector {n : Nat} (element length : CTm Tower.Head n) :
    (vector element length).erase = vecApp element.erase length.erase := rfl

theorem erase_universeMotive {n : Nat} (element : CTm Tower.Head n) :
    (universeMotive element).erase = NativeVectorAll.allUniverseMotive := rfl

theorem erase_consCase {n : Nat} (element predicate : CTm Tower.Head n) :
    (consCase element predicate).erase = NativeVectorAll.allTypeConsCase predicate.erase := by
  simp only [consCase, CTm.erase, weaken4, weaken2, CTm.erase_rename, NativeVectorAll.allTypeConsCase,
    NativeVectorAll.weaken4, Presentation.rename_comp]
  rfl

theorem erase_allType {n : Nat} (element predicate length value : CTm Tower.Head n) :
    (allType element predicate length value).erase = NativeVectorAll.allType element.erase predicate.erase length.erase value.erase := by
  simp only [allType, CTm.erase, erase_universeMotive, erase_consCase, NativeVectorAll.allType,
    NativeVectorAll.unitType, vecEliminateApp, natTm, zeroTm]

theorem substitute_vector {n m : Nat} (images : CSub Tower.Head n m) (element length : CTm Tower.Head n) :
    (vector element length).subst images = vector (element.subst images) (length.subst images) := rfl

theorem substitute_universeMotive {n m : Nat} (images : CSub Tower.Head n m) (element : CTm Tower.Head n) :
    (universeMotive element).subst images = universeMotive (element.subst images) := by
  simp only [universeMotive, vector, CTm.subst, CTm.subst_liftSub_wk, CTm.liftSub, Fin.cases_zero]

theorem substitute_consCase {n m : Nat} (images : CSub Tower.Head n m) (element predicate : CTm Tower.Head n) :
    (consCase element predicate).subst images = consCase (element.subst images) (predicate.subst images) := by
  simp only [consCase, vector, weaken2, weaken4, CTm.subst, CTm.subst_liftSub_wk, CTm.liftSub]
  rfl

theorem substitute_allType {n m : Nat} (images : CSub Tower.Head n m) (element predicate length value : CTm Tower.Head n) :
    (allType element predicate length value).subst images =
      allType (element.subst images) (predicate.subst images) (length.subst images) (value.subst images) := by
  simp only [allType, CTm.subst, substitute_universeMotive, substitute_consCase]

#print axioms erase_allType
#print axioms substitute_allType

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated
