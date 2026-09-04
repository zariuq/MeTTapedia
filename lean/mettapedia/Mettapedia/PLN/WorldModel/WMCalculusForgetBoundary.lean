import Mettapedia.PLN.WorldModel.WMCalculusSoundness

/-!
# The current world-model soundness contract does not constrain forgetting

`WMCalculus` exposes revision, extraction, and an optional forgetting
operation.  Its current `CalculusSound` property proves agreement with the
additive world-model algebra only for revision and extraction.  This module
records the exact boundary with a positive/negative pair.

Two calculi below have definitionally identical revision and extraction and
both satisfy `CalculusSound`.  One has no forgetting operation; the other
installs an arbitrary constant-zero operation.  Thus the existing soundness
property cannot justify any claim about forgetting.

This is intentionally a boundary theorem rather than a guessed repair.
Forgetting may later be specified by provenance masks, a partial subtraction,
a residual, a source-indexed action, or an explicit refusal.  Each choice has
different algebraic requirements and should be a separate property in the
world-model profile.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WMCalculusSoundness

local instance : EvidenceType Nat := {}

local instance : AdditiveWorldModel Nat Unit Nat where
  extract state _query := state
  extract_add _left _right _query := rfl

/-- The additive revision/extraction core with no forgetting operation. -/
def withoutForget : WMCalculus Nat Unit Nat where
  revise := (· + ·)
  extract := fun state _query => state
  forget := none

/-- The same additive core equipped with an arbitrary constant-zero
forgetting operation. -/
def withArbitraryForget : WMCalculus Nat Unit Nat where
  revise := (· + ·)
  extract := fun state _query => state
  forget := some (fun _state _source => 0)

theorem withoutForget_sound : CalculusSound withoutForget where
  revise_correct _left _right := rfl
  extract_correct _state _query := rfl

theorem withArbitraryForget_sound : CalculusSound withArbitraryForget where
  revise_correct _left _right := rfl
  extract_correct _state _query := rfl

/-- The part observed by `CalculusSound` is exactly the same. -/
theorem same_revision_and_extraction :
    (∀ left right,
      withoutForget.revise left right =
        withArbitraryForget.revise left right) ∧
    (∀ state query,
      withoutForget.extract state query =
        withArbitraryForget.extract state query) := by
  constructor
  · intro left right
    rfl
  · intro state query
    rfl

/-- Their optional forgetting operations are nevertheless distinct. -/
theorem forgetting_differs :
    withoutForget.forget ≠ withArbitraryForget.forget := by
  simp [withoutForget, withArbitraryForget]

/-- Main separation: two calculi can share the complete currently certified
core and both satisfy `CalculusSound` while disagreeing about forgetting. -/
theorem current_soundness_does_not_determine_forgetting :
    ∃ first second : WMCalculus Nat Unit Nat,
      CalculusSound first ∧
      CalculusSound second ∧
      (∀ left right, first.revise left right = second.revise left right) ∧
      (∀ state query, first.extract state query = second.extract state query) ∧
      first.forget ≠ second.forget := by
  exact ⟨withoutForget, withArbitraryForget,
    withoutForget_sound, withArbitraryForget_sound,
    same_revision_and_extraction.1,
    same_revision_and_extraction.2,
    forgetting_differs⟩

#print axioms withoutForget_sound
#print axioms withArbitraryForget_sound
#print axioms same_revision_and_extraction
#print axioms forgetting_differs
#print axioms current_soundness_does_not_determine_forgetting

end Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary
