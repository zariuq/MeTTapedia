import Mettapedia.GSLT.LanguageDef.VariableArgumentInstantiation
import Mettapedia.GSLT.LanguageDef.PartialRenamingInstantiationControls

/-!
# Executable recognition and contextual body recovery controls

All signatures are derived from the existing occurrence-control LanguageDef.
Arguments are authored independently of the recognizer. A repeated-variable
example is both rejected by the injective profile and genuinely instantiable.
-/

namespace Mettapedia.GSLT.LanguageDef.VariableArgumentRecognitionControls

open Mettapedia.OSLF.Binding Mettapedia.OSLF.MeTTaIL.Syntax
open MetaDependencyControls ScopedMatcherDependencyBoundary PartialRenamingControls
open PartialRenamingInstantiationControls
open WellSorted.OccurrenceControls (a b)

set_option autoImplicit false

def subsetArgs {M : List (MetaArity signature)} :
    Args (withMetas signature M) [([], a)] [a, a] :=
  .cons (.var (.succ .zero)) .nil

def permutedArgs : Args (withMetas signature binaryDeclarations) [([], a), ([], a)] [a, a] :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def mixedArgs : Args (withMetas signature declarations) [([], a), ([], b)] [b, a, b] :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def diagonalArgs : Args (withMetas signature binaryDeclarations) [([], a), ([], a)] [a] :=
  .cons (.var .zero) (.cons (.var .zero) .nil)

def rigidArgs : Args (withMetas signature declarations) [([], a)] [a, a] :=
  .cons (embed constant) .nil

theorem subset_recognized :
    (recognizeVariableArguments (S := withMetas signature declarations)
      (dependencies := [a]) subsetArgs).isSome = true := rfl

theorem permutation_recognized :
    (recognizeVariableArguments (S := withMetas signature binaryDeclarations)
      (dependencies := [a, a]) permutedArgs).isSome = true := rfl

theorem mixed_sorts_recognized :
    (recognizeVariableArguments (S := withMetas signature declarations)
      (dependencies := [a, b]) mixedArgs).isSome = true := rfl

theorem subset_body_recovered :
    recoverVariableArgumentBody (dependencies := [a]) (subsetArgs (M := declarations))
      (.var (.succ .zero) : Term signature [a, a] a) = some (.var .zero) := rfl

theorem permuted_body_recovered :
    recoverVariableArgumentBody (dependencies := [a, a]) permutedArgs
      (.var (.succ .zero) : Term signature [a, a] a) = some (.var .zero) := rfl

theorem mixed_first_body_recovered :
    recoverVariableArgumentBody (dependencies := [a, b]) mixedArgs
      (.var (.succ .zero) : Term signature [b, a, b] a) = some (.var .zero) := rfl

theorem mixed_second_body_recovered :
    recoverVariableArgumentBody (dependencies := [a, b]) mixedArgs
      (.var .zero : Term signature [b, a, b] b) = some (.var (.succ .zero)) := rfl

theorem mixed_unselected_reference_declined :
    recoverVariableArgumentBody (dependencies := [a, b]) mixedArgs
      (.var (.succ (.succ .zero)) : Term signature [b, a, b] b) = none := rfl

theorem nested_body_recovered :
    recoverVariableArgumentBody (dependencies := [a]) (subsetArgs (M := nestedDeclarations)) nestedSelected =
      some nestedBody := rfl

theorem local_binder_retained :
    recoverVariableArgumentBody (dependencies := [a]) (subsetArgs (M := nestedDeclarations)) locallyBoundSource =
      some locallyBoundResult := rfl

theorem nested_unsupported_reference_declined :
    recoverVariableArgumentBody (dependencies := [a]) (subsetArgs (M := nestedDeclarations)) nestedUnsupported = none := rfl

theorem actual_nested_instantiation :
    instantiate nestedAssignment (.op (.inr (.mk nestedIndex)) subsetArgs) = nestedSelected := by
  cases found : recognizeVariableArguments (S := withMetas signature nestedDeclarations)
      (dependencies := [a]) subsetArgs with
  | none => cases found
  | some selected =>
      exact (recoverVariableArgumentBody_instantiate_iff nestedIndex subsetArgs selected found
        nestedAssignment nestedSelected).mp nested_body_recovered

theorem repeated_arguments_declined : recognizeVariableArguments (S := withMetas signature binaryDeclarations)
      (dependencies := [a, a]) diagonalArgs = none := rfl

theorem nonvariable_argument_declined : recognizeVariableArguments (S := withMetas signature declarations)
      (dependencies := [a]) rigidArgs = none := rfl

/-- Profile rejection is not a general no-solution result. -/
theorem diagonal_has_actual_instantiation :
    instantiate firstBody (.op (.inr (.mk binaryIndex)) diagonalArgs) =
      (.var .zero : Term signature [a] a) := rfl

theorem diagonal_rejected_but_solvable :
    recognizeVariableArguments (S := withMetas signature binaryDeclarations)
      (dependencies := [a, a]) diagonalArgs = none ∧
      ∃ assignment : (i : Fin binaryDeclarations.length) →
          Term signature (binaryDeclarations.get i).1 (binaryDeclarations.get i).2,
        instantiate assignment (.op (.inr (.mk binaryIndex)) diagonalArgs) =
          (.var .zero : Term signature [a] a) :=
  ⟨repeated_arguments_declined, firstBody, diagonal_has_actual_instantiation⟩

end Mettapedia.GSLT.LanguageDef.VariableArgumentRecognitionControls
