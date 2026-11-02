import Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSubstitution
import Mettapedia.Languages.MM0.Kernel.FreshDummies

/-!
# MM0 fresh dummy images checked by native support masks

Typed arguments already have defined support. Under that established
precondition, dummy freshness needs only native support exclusion and the
declared sort of each bound image. Earlier dummy images are added to the
argument set before checking the next image, so freshness includes pairwise
distinctness.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

def checkFreshMask (store : Store Head) (target : Context) (index : Nat) (expression : Preterm) : Bool :=
  let reference := (encodeR store (encode target expression)).2
  ContextualMatching.subCheck reference.thin (excluding reference.thin.length index)

theorem checkFreshMask_eq {store : Store Head} (canonical : Canonical store)
    {target : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports target expression support) (index : Nat) :
    checkFreshMask store target index expression = Preterm.checkFreshFor target index expression := by
  apply Bool.eq_iff_iff.mpr
  rw [checkFreshMask, exclusion_check_exact, Preterm.checkFreshFor_iff]
  constructor
  · intro absent
    refine ⟨⟨support, supported⟩, ?_⟩
    intro used
    have present := (reference_hasVar supported store canonical index).mpr used
    rw [absent] at present
    cases present
  · intro fresh
    cases used : Thin.bit (encodeR store (encode target expression)).2.thin index with
    | false => rfl
    | true => exact False.elim (fresh.2 ((reference_hasVar supported store canonical index).mp used))

def checkDummiesNative (store : Store Head) (target : Context) : List Preterm → List Nat → List Nat → Bool
  | _, [], [] => true
  | arguments, sort :: sorts, image :: images =>
      decide (target[image]? = some (.bound sort)) &&
        arguments.all (checkFreshMask store target image) &&
        checkDummiesNative store target (arguments ++ [.var image]) sorts images
  | _, _, _ => false

theorem checkDummiesNative_eq {store : Store Head} (canonical : Canonical store)
    (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (supported : ∀ expression ∈ arguments, ∃ support, Preterm.Supports target expression support) :
    checkDummiesNative store target arguments sorts images = Definition.checkDummies target arguments sorts images := by
  induction sorts generalizing arguments images with
  | nil => cases images <;> rfl
  | cons sort sorts ih =>
      cases images with
      | nil => rfl
      | cons image images =>
          by_cases boundImage : target[image]? = some (.bound sort)
          · have allChecks : arguments.all (checkFreshMask store target image) =
                arguments.all (Preterm.checkFreshFor target image) := by
              apply Bool.eq_iff_iff.mpr
              simp only [List.all_eq_true]
              apply forall_congr'
              intro expression
              apply forall_congr'
              intro member
              obtain ⟨support, scopedExpression⟩ := supported expression member
              rw [checkFreshMask_eq canonical scopedExpression]
            have extended : ∀ expression ∈ arguments ++ [.var image],
                ∃ support, Preterm.Supports target expression support := by
              intro expression member
              rcases List.mem_append.mp member with old | fresh
              · exact supported expression old
              · have same : expression = .var image := by simpa using fresh
                subst expression
                exact ⟨_, .bound boundImage⟩
            simp only [checkDummiesNative, Definition.checkDummies, boundImage, decide_true, Bool.true_and,
              allChecks, ih _ images extended]
          · simp [checkDummiesNative, Definition.checkDummies, boundImage]

theorem checkDummiesNative_iff {store : Store Head} (canonical : Canonical store)
    (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (supported : ∀ expression ∈ arguments, ∃ support, Preterm.Supports target expression support) :
    checkDummiesNative store target arguments sorts images = true ↔
      Definition.FreshDummies target arguments sorts images := by
  rw [checkDummiesNative_eq canonical target arguments sorts images supported, Definition.checkDummies_iff]

namespace DummyControls

def target : Context := [.bound 0, .bound 0, .regular 0 {0}]

theorem fresh_distinct_images_accepted : checkDummiesNative [] target [] [0, 0] [0, 1] = true := by
  rw [checkDummiesNative_eq canonical_nil target [] [0, 0] [0, 1] (by simp)]
  decide

theorem repeated_image_refused : checkDummiesNative [] target [] [0, 0] [0, 0] = false := by
  rw [checkDummiesNative_eq canonical_nil target [] [0, 0] [0, 0] (by simp)]
  decide

theorem dependency_hidden_in_regular_argument_refused :
    checkDummiesNative [] target [.var 2] [0] [0] = false := by
  rw [checkDummiesNative_eq canonical_nil target [.var 2] [0] [0] (by
    intro expression member
    have same : expression = .var 2 := by simpa using member
    subst expression
    exact ⟨_, .regular rfl⟩)]
  decide

theorem wrong_dummy_sort_refused : checkDummiesNative [] target [] [1] [0] = false := by
  decide

end DummyControls

end Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport
