import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaComparison
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationNames

/-!
# Alpha-test and operand-selection normalization contracts

The comparator is the existing executable global variant solver through the
atom codec. Well-formed calls reuse the Boolean and selection combinators.
Wrong arity produces the native-shaped Error call and fixed reason, rather
than silently becoming an unavailable operation. These are value-projection
laws; the native raised-result marker, scalar codecs and graph-walker
implementation remain separately observed boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaNormalization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open TypeDependencyAdmission
open TypeNormalizationScope
open TypeNormalizationNames

def arityError (head : String) (args : List Atom) : Atom :=
  .expression [.symbol "Error", .expression (.symbol head :: args), .symbol "IncorrectNumberOfArguments"]

def finish (head : String) (args : List Atom) (result : Option Atom) : Atom :=
  result.getD (arityError head args)

def active (head : String) : Bool := head == "=alpha" || head == "if-equal"

def dispatch : Primitive := fun head args =>
  if head = "=alpha" then some (finish head args (booleanResult TypeAlphaComparison.check args))
  else if head = "if-equal" then some (finish head args (chooseResult TypeAlphaComparison.check args))
  else none

theorem arityError_support (head : String) (args : List Atom) :
    atomVariables (arityError head args) = atomListVariables args := by
  simp [arityError, atomVariables, atomListVariables]

theorem arityError_closed (head : String) (args : List Atom) (safe : resourceFreeList args = true) :
    resourceFree (arityError head args) = true := by
  simp [arityError, resourceFree, resourceFreeList, safe]

theorem arityError_rename (permutation : Equiv.Perm String) (head : String) (args : List Atom) :
    arityError head (renameAtomList permutation args) = renameAtom permutation (arityError head args) := by
  simp [arityError, renameAtom, renameAtomList]

theorem finish_support (head : String) (args : List Atom) (result : Option Atom)
    (supported : ∀ atom, result = some atom → atomVariables atom ⊆ atomListVariables args) :
    atomVariables (finish head args result) ⊆ atomListVariables args := by
  cases result with
  | none =>
      rw [finish, Option.getD_none, arityError_support]
      exact fun _ member => member
  | some atom => exact supported atom rfl

theorem finish_closed (head : String) (args : List Atom) (safe : resourceFreeList args = true)
    (result : Option Atom) (closed : ∀ atom, result = some atom → resourceFree atom = true) :
    resourceFree (finish head args result) = true := by
  cases result with
  | none => exact arityError_closed head args safe
  | some atom => exact closed atom rfl

theorem finish_rename (permutation : Equiv.Perm String) (head : String) (args : List Atom) (result : Option Atom) :
    finish head (renameAtomList permutation args) (result.map (renameAtom permutation)) =
      renameAtom permutation (finish head args result) := by
  cases result with
  | none => exact arityError_rename permutation head args
  | some atom => rfl

theorem comparison_equivariant : ComparisonEquivariant TypeAlphaComparison.check :=
  TypeAlphaComparison.equivariant

theorem results_supported : ResultsSupported active dispatch := by
  intro head args _ result returned
  unfold dispatch at returned
  split at returned
  · cases Option.some.inj returned
    exact finish_support head args _ (booleanResult_support _ args)
  · split at returned
    · cases Option.some.inj returned
      exact finish_support head args _ (chooseResult_support _ args)
    · contradiction

theorem results_closed : ResultsClosed active dispatch := by
  intro head args _ safe result returned
  unfold dispatch at returned
  split at returned
  · cases Option.some.inj returned
    exact finish_closed head args safe _ (booleanResult_closed _ args)
  · split at returned
    · cases Option.some.inj returned
      exact finish_closed head args safe _ (chooseResult_closed _ args safe)
    · contradiction

theorem equivariant : Equivariant active dispatch := by
  intro permutation head args _
  unfold dispatch
  split
  · rw [booleanResult_equivariant _ comparison_equivariant permutation args, finish_rename]
    rfl
  · split
    · rw [chooseResult_equivariant _ comparison_equivariant permutation args, finish_rename]
      rfl
    · rfl

theorem normalization_keeps_names (world : RetainedTypePayloads.ExternalView) (atom : Atom)
    (safe : resourceFree atom = true) :
    atomVariables (InertTypeDependencies.normalize active (observed world dispatch) atom) ⊆ atomVariables atom :=
  normalize_observed_support active dispatch results_closed results_supported world atom safe

theorem normalization_renames (world : RetainedTypePayloads.ExternalView) (permutation : Equiv.Perm String)
    (atom : Atom) (safe : resourceFree atom = true) :
    InertTypeDependencies.normalize active (observed world dispatch) (renameAtom permutation atom) =
      renameAtom permutation (InertTypeDependencies.normalize active (observed world dispatch) atom) :=
  normalize_observed_equivariant active dispatch results_closed equivariant world permutation atom safe

theorem next_read_cannot_capture_normalized_names (world : RetainedTypePayloads.ExternalView)
    (supply : TypeReadSupply.Supply) (first second : Atom) (safe : resourceFree first = true)
    (name : String) (member : name ∈ atomVariables
      (InertTypeDependencies.normalize active (observed world dispatch) (TypeReadSupply.fresh supply first).1)) :
    name ∉ atomVariables (TypeReadSupply.fresh (TypeReadSupply.fresh supply first).2 second).1 :=
  observed_normalized_before_later_read active dispatch results_closed results_supported world supply
    first second safe name member

namespace Controls

def selector : Atom := .expression [.symbol "if-equal",
  TypeAlphaComparison.Controls.pair (.var "a") (.var "b"),
  TypeAlphaComparison.Controls.pair (.var "b") (.var "a"), .var "keep", .var "other"]

theorem alpha_selection_keeps_selected_operand :
    InertTypeDependencies.normalize active dispatch selector = .var "keep" := by cbv

theorem malformed_arity_is_an_error_not_decline :
    dispatch "=alpha" [.var "x", .var "x", .var "extra"] =
      some (arityError "=alpha" [.var "x", .var "x", .var "extra"]) := rfl

theorem error_retains_original_argument_variables :
    atomVariables (finish "=alpha" [.var "x", .var "x", .var "extra"] none) =
      ["x", "x", "extra"] := rfl

theorem normalizer_does_not_dispatch_short_forms :
    InertTypeDependencies.normalize active dispatch (.expression [.symbol "=alpha", .var "x"]) =
      .expression [.symbol "=alpha", .var "x"] := by cbv

theorem a_different_sharing_pattern_selects_other_operand :
    dispatch "if-equal" [TypeAlphaComparison.Controls.pair (.var "a") (.var "a"),
      TypeAlphaComparison.Controls.pair (.var "b") (.var "c"), .symbol "same", .symbol "different"] =
      some (.symbol "different") := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaNormalization
