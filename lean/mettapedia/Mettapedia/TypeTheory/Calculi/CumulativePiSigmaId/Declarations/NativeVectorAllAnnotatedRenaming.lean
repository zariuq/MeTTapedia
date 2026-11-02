import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedTransport

/-!
# Renaming the original annotated All program

The source program, including its universe motive and branch annotations,
commutes with every scoped renaming. This follows from its substitution law;
it requires no computation rule or equality-reflection assumption.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated

theorem allType_rename {n m : Nat} (result : LevelExpr Nat)
    (A predicate length value : CTm Tower.Head n) (rho : Ren n m) :
    (allType result A predicate length value).rename rho =
      allType result (A.rename rho) (predicate.rename rho) (length.rename rho) (value.rename rho) := by
  have renamed (term : CTm Tower.Head n) :
      term.rename rho = term.subst (fun index => .var (rho index)) := by
    simpa only [CTm.subst_ids, CTm.ids, CTm.rename] using CTm.rename_subst rho CTm.ids term
  simpa only [← renamed] using
    (allType_substitute result A predicate length value (fun index => .var (rho index)))

#print axioms allType_rename

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation
