import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeFreshReadEquivalence
import Mettapedia.Logic.LP.VariantMatching

/-!
# Executable alpha comparison for the type-query carrier

The existing structural variant solver supplies one consistent variable map
for the entire term. Its decision is equivalent to a permutation of the
finite variable support and to the independent HE observed-type alpha
relation. This instantiates the alpha-comparison parameter used by subtype
cycle checks and primitive selection. It does not equate opaque native
equality with structural equality or verify a native graph walker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaComparison

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Logic.LP (Term Subst)
open Mettapedia.Logic.LP.StructuralTestRenaming (Variant)
open TypeScopeRenaming

def check (left right : Atom) : Bool :=
  (Mettapedia.Logic.LP.VariantMatching.solve [UnifyAtoms.encode left] [UnifyAtoms.encode right]).isSome

theorem check_iff_variant (left right : Atom) :
    check left right = true ↔ Variant (UnifyAtoms.encode left) (UnifyAtoms.encode right) := by
  rw [check, Option.isSome_iff_exists]
  constructor
  · rintro ⟨pairs, accepted⟩
    have result := Mettapedia.Logic.LP.VariantMatching.solve_sound _ _ pairs accepted
    exact (Mettapedia.Logic.LP.VariantMatching.singleton_iff (σ := UnifyAtoms.sig) _ _).mp
      ⟨Mettapedia.Logic.LP.VariantMatching.lookup pairs, result.2⟩
  · intro variant
    exact Mettapedia.Logic.LP.VariantMatching.solve_complete _ _
      ((Mettapedia.Logic.LP.VariantMatching.singleton_iff (σ := UnifyAtoms.sig) _ _).mpr variant)

theorem check_iff_permutation (left right : Atom) :
    check left right = true ↔ ∃ permutation : Equiv.Perm String, renameAtom permutation left = right := by
  rw [check_iff_variant]
  constructor
  · rintro ⟨rename, injective, same⟩
    classical
    let support := (UnifyAtoms.encode left).freeVars
    let image : support → String := fun name => rename name.val
    have imageInjective : Function.Injective image := by
      intro first second equal
      apply Subtype.ext
      exact injective first.property second.property equal
    obtain ⟨permutation, agrees⟩ := Equiv.Perm.exists_extending_pair
      (fun name : support => name.val) image Subtype.val_injective imageInjective
    have renamed : Mettapedia.Logic.LP.UnificationRenaming.rename permutation (UnifyAtoms.encode left) =
        Mettapedia.Logic.LP.UnificationRenaming.rename rename (UnifyAtoms.encode left) := by
      apply Mettapedia.Logic.LP.Subst.applyTerm_congr
      intro name member
      exact congrArg Term.var (agrees ⟨name, member⟩)
    refine ⟨permutation, ?_⟩
    have decoded := congrArg UnifyAtoms.decode (renamed.trans same)
    simpa only [decode_rename, UnifyAtoms.decode_encode] using decoded
  · rintro ⟨permutation, same⟩
    refine ⟨permutation, fun _ _ _ _ equal => permutation.injective equal, ?_⟩
    rw [← encode_rename, same]

theorem check_iff_observed_alpha (left right : Atom) :
    check left right = true ↔ ObservedTypeAlphaRel left right := by
  rw [check_iff_permutation]
  constructor
  · rintro ⟨permutation, same⟩
    refine ⟨left, TypeVariableRenamingOf.refl left, permutation, permutation.injective, ?_⟩
    rw [← TypeFreshReadEquivalence.atom_rename_presentation]
    exact same.symm
  · intro alpha
    obtain ⟨permutation, same⟩ := ScopeObservation.ObservedTypeAlphaRel.exists_permutation alpha
    refine ⟨permutation, ?_⟩
    rw [TypeFreshReadEquivalence.atom_rename_presentation]
    exact same.symm

theorem equivariant (permutation : Equiv.Perm String) (left right : Atom) :
    check (renameAtom permutation left) (renameAtom permutation right) = check left right := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff_variant, check_iff_variant, encode_rename, encode_rename]
  exact Mettapedia.Logic.LP.StructuralTestRenaming.variant_rename_iff
    (σ := UnifyAtoms.sig) permutation permutation.symm permutation.left_inv _ _

theorem reflexive (type_ : Atom) : check type_ type_ = true :=
  (check_iff_observed_alpha _ _).mpr (.refl type_)

theorem symmetric (left right : Atom) : check left right = check right left := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff_observed_alpha, check_iff_observed_alpha]
  exact ⟨ObservedTypeAlphaRel.symm, ObservedTypeAlphaRel.symm⟩

namespace Controls

def pair (left right : Atom) : Atom := .expression [.symbol "Pair", left, right]

theorem swapping_names_is_not_a_logical_cycle :
    check (pair (.var "a") (.var "b")) (pair (.var "b") (.var "a")) = true := by cbv

theorem shared_variables_cannot_be_split :
    check (pair (.var "a") (.var "a")) (pair (.var "b") (.var "c")) = false := by cbv

theorem independent_variables_cannot_be_merged :
    check (pair (.var "a") (.var "b")) (pair (.var "c") (.var "c")) = false := by cbv

theorem scalar_values_and_kinds_remain_observable :
    check (.expression [.symbol "F", .grounded (.int 1)])
      (.expression [.symbol "F", .grounded (.string "1")]) = false ∧
    check (.expression [.symbol "F", .grounded (.int 1)])
      (.expression [.symbol "F", .grounded (.int 2)]) = false := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaComparison
