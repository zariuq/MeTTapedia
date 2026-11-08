import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeRenaming
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupplyVariants
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation

/-!
# Different lawful private allocators preserve ordered type admission

Two independently allocated candidate families are compared by the existing
public-fixed permutation theorem. The actual ordered type matcher then
transports its selected substitution. Public expected-type variables are
fixed, candidate positions are not reordered, and no completed-result oracle
is introduced. This connects fresh-instance evidence to an operational
matching result rather than just to a syntactic alpha judgment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeFreshReadEquivalence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
open TypeDependencyAdmission TypeScopeMatcher TypeScopeRenaming
open RetainedTypePayloads (ExternalView)

mutual
theorem atom_rename_presentation (rename : String → String) : ∀ atom,
    renameAtom rename atom = renameTypeVars rename atom
  | .symbol _ => by simp [renameAtom, renameTypeVars]
  | .var _ => by simp [renameAtom, renameTypeVars]
  | .grounded _ => by simp [renameAtom, renameTypeVars]
  | .expression children => by
      simp only [renameAtom, renameTypeVars]
      exact congrArg Atom.expression (list_rename_presentation rename children)
theorem list_rename_presentation (rename : String → String) : ∀ atoms,
    renameAtomList rename atoms = atoms.map (renameTypeVars rename)
  | [] => rfl
  | atom :: atoms => by
      rw [renameAtomList, List.map_cons, atom_rename_presentation, list_rename_presentation]
end

theorem initial_state_fixed (permutation : Equiv.Perm String) : renameState permutation Atom.var = Atom.var := by
  funext name
  simp [renameState, renameAtom]

theorem expected_fixed (permutation : Equiv.Perm String) (scope : List String)
    (fixed : ∀ name ∈ scope, permutation name = name) (expected : Atom)
    (covered : TypeSubst.typeVars expected ⊆ scope) : renameAtom permutation expected = expected := by
  rw [atom_rename_presentation]
  calc
    renameTypeVars permutation expected = renameTypeVars id expected :=
      renameTypeVars_congr_on_typeVars expected (fun name member => fixed name (covered member))
    _ = expected := renameTypeVars_id expected

theorem firstChoice_private_allocators (world : ExternalView) (scope : List String)
    (sources left right : List Atom)
    (leftVariant : ArgumentAlphaVariantsRel scope sources left)
    (rightVariant : ArgumentAlphaVariantsRel scope sources right)
    (leftSafe : resourceFreeList left = true) (expected : Atom)
    (expectedSafe : resourceFree expected = true) (covered : TypeSubst.typeVars expected ⊆ scope) :
    ∃ permutation : Equiv.Perm String,
      (∀ name ∈ scope, permutation name = name) ∧
      right = left.map (renameAtom permutation) ∧
      StampInference.firstResult (fun actual => unify world Atom.var actual expected) right =
        (StampInference.firstResult (fun actual => unify world Atom.var actual expected) left).map
          (renameState permutation) := by
  obtain ⟨permutation, fixed, renamed⟩ :=
    ScopeObservation.argumentAlphaVariants_public_fixed_permutation leftVariant rightVariant
  have renamedAtoms : right = left.map (renameAtom permutation) := by
    rw [show renameAtom permutation = renameTypeVars permutation from funext (atom_rename_presentation permutation)]
    exact renamed
  refine ⟨permutation, fixed, renamedAtoms, ?_⟩
  have transported := firstChoice_rename world permutation Atom.var (fun _ => rfl)
    expected expectedSafe left leftSafe
  simpa only [initial_state_fixed, expected_fixed permutation scope fixed expected covered, ← renamedAtoms] using transported

theorem private_allocation_preserves_admission (world : ExternalView) (scope : List String)
    (sources left right : List Atom)
    (leftVariant : ArgumentAlphaVariantsRel scope sources left)
    (rightVariant : ArgumentAlphaVariantsRel scope sources right)
    (leftSafe : resourceFreeList left = true) (expected : Atom)
    (expectedSafe : resourceFree expected = true) (covered : TypeSubst.typeVars expected ⊆ scope) :
    (StampInference.firstResult (fun actual => unify world Atom.var actual expected) right).isSome =
      (StampInference.firstResult (fun actual => unify world Atom.var actual expected) left).isSome := by
  obtain ⟨permutation, _, _, same⟩ := firstChoice_private_allocators world scope sources left right
    leftVariant rightVariant leftSafe expected expectedSafe covered
  rw [same, Option.isSome_map]

theorem chosen_range_private_allocators (world : ExternalView) (scope : List String)
    (sources left right : List Atom)
    (leftVariant : ArgumentAlphaVariantsRel scope sources left)
    (rightVariant : ArgumentAlphaVariantsRel scope sources right)
    (leftSafe : resourceFreeList left = true) (expected range : Atom)
    (expectedSafe : resourceFree expected = true) (expectedCovered : TypeSubst.typeVars expected ⊆ scope)
    (rangeCovered : TypeSubst.typeVars range ⊆ scope) :
    ∃ permutation : Equiv.Perm String,
      (∀ name ∈ scope, permutation name = name) ∧
      (StampInference.firstResult (fun actual => unify world Atom.var actual expected) right).map
          (fun state => substA state range) =
        (StampInference.firstResult (fun actual => unify world Atom.var actual expected) left).map
          (fun state => renameAtom permutation (substA state range)) := by
  obtain ⟨permutation, fixed, _, same⟩ := firstChoice_private_allocators world scope sources left right
    leftVariant rightVariant leftSafe expected expectedSafe expectedCovered
  refine ⟨permutation, fixed, ?_⟩
  rw [same, Option.map_map]
  apply congrArg (fun f => Option.map f _)
  funext state
  change substA (renameState permutation state) range = _
  have transport := substitute permutation state range
  rw [expected_fixed permutation scope fixed range rangeCovered] at transport
  exact transport

theorem generated_supplies_preserve_admission (world : ExternalView)
    (first second : TypeReadSupply.Supply) (sameScope : first.used = second.used)
    (sources : List Atom) (sourcesSafe : resourceFreeList sources = true)
    (expected : Atom) (expectedSafe : resourceFree expected = true)
    (covered : TypeSubst.typeVars expected ⊆ first.used) :
    (StampInference.firstResult (fun actual => unify world Atom.var actual expected)
      (TypeReadSupply.freshList first sources).1).isSome =
    (StampInference.firstResult (fun actual => unify world Atom.var actual expected)
      (TypeReadSupply.freshList second sources).1).isSome := by
  have secondVariant : ArgumentAlphaVariantsRel first.used sources (TypeReadSupply.freshList second sources).1 := by
    rw [sameScope]
    exact TypeReadSupply.freshList_variants second sources
  exact (private_allocation_preserves_admission world first.used sources _ _
    (TypeReadSupply.freshList_variants first sources) secondVariant
    (TypeReadSupply.freshList_resourceFree first sources sourcesSafe) expected expectedSafe covered).symm

namespace Controls

def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]
def sources : List Atom := [.symbol "WrongHead", pair (.symbol "String") (.var "element")]
def expected : Atom := pair (.var "public") (.symbol "Number")
def first : TypeReadSupply.Supply := ⟨["public"], 0⟩
def second : TypeReadSupply.Supply := ⟨["public"], 9⟩
def world : ExternalView := fun tag key => .grounded (.custom tag key)

def chosen (actuals : List Atom) : Option Atom :=
  (StampInference.firstResult (fun actual => unify world Atom.var actual expected) actuals).map
    (fun state => state "public")

theorem independent_supplies_keep_public_return :
    chosen (TypeReadSupply.freshList first sources).1 = some (.symbol "String") ∧
    chosen (TypeReadSupply.freshList second sources).1 = some (.symbol "String") := by cbv

theorem public_capture_changes_admission :
    chosen [pair (.symbol "String") (.var "public")] = none ∧
    chosen (TypeReadSupply.freshList first sources).1 ≠ none := by
  constructor
  · cbv
  · rw [independent_supplies_keep_public_return.1]
    simp

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeFreshReadEquivalence
