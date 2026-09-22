import Mettapedia.OSLF.Syntax.BoundPrefixProjection
import Mettapedia.GSLT.LanguageDef.VariableArgumentRecognitionControls

/-!
# Bound-prefix projection with a nonempty ordinary context

These are actual arguments over the LanguageDef-derived signature. The ordinary
context remains nonempty, including variables with the very same sort as bound
arguments. Projection and variable recognition remain separate operations.
-/

namespace Mettapedia.GSLT.LanguageDef.BoundPrefixProjectionControls

open Mettapedia.OSLF.Binding Mettapedia.OSLF.MeTTaIL.Syntax
open MetaDependencyControls ScopedMatcherDependencyBoundary PartialRenamingControls
open PartialRenamingInstantiationControls VariableArgumentRecognitionControls
open WellSorted.OccurrenceControls (a b)

set_option autoImplicit false

def subsetWithOrdinary : Args (withMetas signature nestedDeclarations) [([], a)]
    ([a, a] ++ [a, b]) := .cons (.var (.succ .zero)) .nil

def permutationWithOrdinary : Args (withMetas signature binaryDeclarations)
    [([], a), ([], a)] ([a, a] ++ [a, b]) :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def mixedWithOrdinary : Args (withMetas signature declarations)
    [([], a), ([], b)] ([b, a, b] ++ [a, b]) :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def ordinarySameSort : Args (withMetas signature nestedDeclarations) [([], a)]
    ([a, a] ++ [a, b]) := .cons (.var (.succ (.succ .zero))) .nil

def ordinaryOtherSort : Args (withMetas signature declarations) [([], b)]
    ([b, a, b] ++ [a, b]) :=
  .cons (.var (.succ (.succ (.succ (.succ .zero))))) .nil

def diagonalWithOrdinary : Args (withMetas signature binaryDeclarations)
    [([], a), ([], a)] ([a] ++ [a, b]) :=
  .cons (.var .zero) (.cons (.var .zero) .nil)

theorem subset_projects :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature nestedDeclarations)
      [a, a] [a, b]) subsetWithOrdinary = some subsetArgs := rfl

theorem permutation_projects :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature binaryDeclarations)
      [a, a] [a, b]) permutationWithOrdinary = some permutedArgs := rfl

theorem mixed_projects :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature declarations)
      [b, a, b] [a, b]) mixedWithOrdinary = some mixedArgs := rfl

theorem original_prefix_projects :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature binaryDeclarations)
      [a, a] [a, b]) (prefixArgs (T := withMetas signature binaryDeclarations) [a, a]) =
      some (idArgs (S := signature) (M := binaryDeclarations) [a, a]) := rfl

theorem ordinary_same_sort_declined :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature nestedDeclarations)
      [a, a] [a, b]) ordinarySameSort = none := rfl

theorem ordinary_other_sort_declined :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature declarations)
      [b, a, b] [a, b]) ordinaryOtherSort = none := rfl

theorem ordinary_argument_has_no_prefix_preimage :
    ¬ ∃ projected, renameArgs
      (fun _ v => injPrefix (S := withMetas signature nestedDeclarations)
        (Γ := [a, b]) [a, a] v) projected = ordinarySameSort :=
  (strengthenA_boundPrefix_none_iff ordinarySameSort).mp ordinary_same_sort_declined

/-- Same result sort and successful generic recognition do not make an ordinary
rule variable a bound variable. -/
theorem ordinary_recognized_but_not_bound :
    (recognizeVariableArguments (S := withMetas signature nestedDeclarations)
      (dependencies := [a]) ordinarySameSort).isSome = true ∧
    strengthenA (Strengthener.boundPrefix (S := withMetas signature nestedDeclarations)
      [a, a] [a, b]) ordinarySameSort = none := ⟨rfl, rfl⟩

/-- Every closing substitution is permitted: the projected body never reads Γ. -/
theorem nested_slot_reads_back (sigma : Sub signature [a, b] []) :
    bind (liftSub sigma [a, a])
      (instantiate nestedAssignment (.op (.inr (.mk nestedIndex)) subsetWithOrdinary)) =
      nestedSelected := by
  cases recognized : recognizeVariableArguments (S := withMetas signature nestedDeclarations)
      (dependencies := [a]) subsetArgs with
  | none => cases recognized
  | some selected =>
      exact projected_recovery_reads_slot subsetWithOrdinary subsetArgs subset_projects
        selected recognized nestedAssignment nestedSelected nestedBody (by rfl) sigma

theorem permutation_slot_reads_back (sigma : Sub signature [a, b] []) :
    bind (liftSub sigma [a, a])
      (instantiate firstBody (.op (.inr (.mk binaryIndex)) permutationWithOrdinary)) =
      (.var (.succ .zero) : Term signature [a, a] a) := by
  cases recognized : recognizeVariableArguments (S := withMetas signature binaryDeclarations)
      (dependencies := [a, a]) permutedArgs with
  | none => cases recognized
  | some selected =>
      exact projected_recovery_reads_slot (bs := [a, a]) (Γ := [a, b])
        (dependencies := [a, a]) permutationWithOrdinary permutedArgs permutation_projects
        selected recognized firstBody
        (.var (.succ .zero) : Term signature ([a, a] ++ []) a)
        (.var .zero) (by rfl) sigma

theorem mixed_slot_reads_back (sigma : Sub signature [a, b] []) :
    bind (liftSub sigma [b, a, b])
      (bind (argsToSub (S := signature) (bs := [a, b])
        (instantiateArgs usesArgument mixedWithOrdinary))
        (.var (.succ .zero) : Term signature [a, b] b)) =
      (.var .zero : Term signature [b, a, b] b) := by
  cases recognized : recognizeVariableArguments (S := withMetas signature declarations)
      (dependencies := [a, b]) mixedArgs with
  | none => cases recognized
  | some selected =>
      exact projected_recovery_reads_slot (bs := [b, a, b]) (Γ := [a, b])
        (dependencies := [a, b]) mixedWithOrdinary mixedArgs mixed_projects
        selected recognized usesArgument
        (.var .zero : Term signature ([b, a, b] ++ []) b)
        (.var (.succ .zero)) (by rfl) sigma

theorem diagonal_projects :
    strengthenA (Strengthener.boundPrefix (S := withMetas signature binaryDeclarations)
      [a] [a, b]) diagonalWithOrdinary = some diagonalArgs := rfl

/-- Projection accepts repeated bound variables, but the subsequent injective
profile rejects them. The original instantiation still has a solution. -/
theorem projected_diagonal_rejected_but_solvable :
    recognizeVariableArguments (S := withMetas signature binaryDeclarations)
      (dependencies := [a, a]) diagonalArgs = none ∧
    instantiate firstBody (.op (.inr (.mk binaryIndex)) diagonalWithOrdinary) =
      (.var .zero : Term signature ([a] ++ [a, b]) a) := ⟨rfl, rfl⟩

end Mettapedia.GSLT.LanguageDef.BoundPrefixProjectionControls
