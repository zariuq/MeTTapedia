import Mettapedia.Languages.OpenTheory.PackageDefinitionOwnership

/-!
# Controls for package-level OpenTheory definition ownership

The positive controls distinguish provenance identity from printed-name
ownership.  The negative control exercises the exact cross-package clash that
is rejected by the pinned package-combination layer.
-/

namespace Mettapedia.Languages.OpenTheory.PackageDefinitionOwnershipCanary

open Mettapedia.Languages.OpenTheory

def sharedName : Name := Name.global "shared"

def freshName : Name := Name.global "fresh"

theorem freshName_ne_sharedName : freshName ≠ sharedName := by
  simp [freshName, sharedName, Name.global]

/-- Package zero already owns the constant spelling `shared`, but no type
operator spelling. -/
def initialOwnership : DefinitionOwnership Nat :=
  fun name =>
    if name = .constant sharedName then some 0 else none

def compatibleDefinitionNames : List DefinedSymbolName :=
  [.constant sharedName, .typeOperator sharedName, .constant freshName]

/-- Repeating ownership inside one package is accepted, and equal printed
spelling across the separate constant/type-operator namespaces is accepted. -/
theorem same_package_and_separate_namespace_admitted :
    (DefinitionOwnership.addDefinitions initialOwnership 0
      compatibleDefinitionNames).isSome = true := by
  rw [DefinitionOwnership.addDefinitions_isSome_iff]
  intro name member
  simp only [compatibleDefinitionNames, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [initialOwnership, freshName_ne_sharedName]

/-- Every name from the accepted package list has the selected owner. -/
theorem accepted_names_are_owned
    {result : DefinitionOwnership Nat}
    (accepted : DefinitionOwnership.addDefinitions initialOwnership 0
      compatibleDefinitionNames = some result) :
    result (.constant sharedName) = some 0 ∧
      result (.typeOperator sharedName) = some 0 ∧
      result (.constant freshName) = some 0 := by
  constructor
  · exact DefinitionOwnership.owns_of_addDefinitions accepted (by
      simp [compatibleDefinitionNames])
  constructor
  · exact DefinitionOwnership.owns_of_addDefinitions accepted (by
      simp [compatibleDefinitionNames])
  · exact DefinitionOwnership.owns_of_addDefinitions accepted (by
      simp [compatibleDefinitionNames])

/-- The same constant spelling cannot be claimed by another package. -/
theorem cross_package_constant_rejected :
    DefinitionOwnership.addDefinitions initialOwnership 1
      [.constant sharedName] = none := by
  exact DefinitionOwnership.addDefinitions_eq_none_of_cross_package
    initialOwnership (package := 1) (existing := 0) (by decide)
    [.constant sharedName] (name := .constant sharedName) (by simp)
    (by simp [initialOwnership])

/-- A type-operator with the same spelling remains available to another
package because OpenTheory keeps the two symbol namespaces distinct. -/
theorem cross_package_other_namespace_admitted :
    (DefinitionOwnership.addDefinitions initialOwnership 1
      [.typeOperator sharedName]).isSome = true := by
  rw [DefinitionOwnership.addDefinitions_isSome_iff]
  intro name member
  simp only [List.mem_singleton] at member
  subst name
  simp [initialOwnership]

end Mettapedia.Languages.OpenTheory.PackageDefinitionOwnershipCanary
