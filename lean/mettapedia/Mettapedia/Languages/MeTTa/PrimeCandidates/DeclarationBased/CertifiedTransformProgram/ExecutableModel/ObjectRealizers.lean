import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectShape
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Realizers

/-!
# The object package on the realizer side

The realizers of the normalization proof are terms of the object package under
its own reduction (`objectRealizers`). That reduction reflects renaming: every
computation of the package, and the decoder, is left-linear and headed by a
constant. The numerals are constructors, and the decoder's steps are steps of
the package's computation. Every computing constant of the object package takes
at least one argument, so a constant that does not compute is strongly
normalizing (`const_sn`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative

namespace CodeModel

/-- The root computation of the object package reflects renaming. -/
theorem objectReflects : RootReflectsRename objectRules.computation := by
  refine RootReflectsRename.union (RootReflectsRename.unionAll fun entry mem => ?_)
    (decoderComputation_reflectsRename _)
  have mem' := (List.mem_filter.mp mem).1
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem'
  rcases mem' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_reflectsRename _ _
  · exact recursionComputation_reflectsRename _ _ _ _ _ _
  · exact recursionComputation_reflectsRename _ _ _ _ _ _
  · exact eliminatorComputation_reflectsRename _
  · exact definitionComputation_reflectsRename _ _ _
  · exact definitionComputation_reflectsRename _ _ _
  · exact definitionComputation_reflectsRename _ _ _
  · exact definitionComputation_reflectsRename _ _ _
  · exact definitionComputation_reflectsRename _ _ _
  · exact recursionComputation_reflectsRename _ _ _ _ _ _
  · exact definitionComputation_reflectsRename _ _ _
  · exact definitionComputation_reflectsRename _ _ _

/-- The numerals of the object package are constructors. -/
theorem objectNumerals : NumeralRoles objectRoles zeroN sucN :=
  ⟨objectRoles_zero, objectRoles_suc⟩

/-- A decoder step is a step of the object package's computation. -/
theorem objectDecodes {n : Nat} {l r : Tower.Tm n}
    (step : DecoderStep programCodes.decoders l r) : objectRules.computation.step l r :=
  .inr step

/-- **The object package as the realizer side.** -/
def objectRealizers : Realizability.Realizers Tower.Head where
  rules := objectRules
  roles := objectRoles
  decoders := programCodes.decoders
  zero := zeroN
  suc := sucN
  shape := objectShape
  reflects := objectReflects
  decoderRoles := objectDecoderRoles
  numerals := objectNumerals
  decodes := objectDecodes

/-- The type of codes is rigid in the object package. -/
theorem objectRoles_prop : objectRoles propN = .rigid :=
  (objectRoles_of (by decide) (by decide) SetProfile.allInstance?_propName
    SetProfile.eqInstance?_propName).trans (roles_of_not_mem (by decide))

/-- A constant that does not compute is strongly normalizing. -/
theorem const_sn {c : DeclName}
    (stuck : ∀ arity scrutinee, objectRoles c ≠ .computes arity scrutinee) {n : Nat} :
    SN objectRules (.const c : Tower.Tm n) :=
  SN.constSpine objectShape (args := []) (fun a s role => absurd role (stuck a s)) (by simp)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
