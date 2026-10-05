import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredCommunication
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction

/-!
# Boundaries of the named and authored pi presentations

The named reduction relation and the LanguageDef-generated internal relation
are separate operational objects. The controls below compare their actual
substitution and execution behavior; they do not assume an adequacy theorem.

Capture-avoiding named substitution agrees with locally nameless substitution
on shadowing, colliding, and disjoint binders. A colliding alpha-renaming also
agrees with the locally nameless representation; the un-freshened target does
not. These are discriminating controls for the general binding laws.

Restriction descent is authored. Input guards still prevent body evaluation,
and raw reducts retain their parallel bag representation. The named relation
uses structural congruence, so its unit-reduced endpoint need not be a raw
engine endpoint. The last controls expose this representation boundary;
they do not assert failure of a modulo-equations comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PresentationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.TypeSynthesis
open PiCalcInstance

def shadowSource : Process := .input "x" "x" (.output "x" "a")

/-- The subject changes while the occurrence bound by that input stays bound. -/
theorem shadow_substitution_preserves_bound_occurrence :
    shadowSource.substitute "x" "z" = .input "z" "x" (.output "x" "a") := by
  decide +kernel

/-- A shadowing binder agrees with locally nameless free-name replacement. -/
theorem shadow_substitution_agrees_with_pattern :
    piToPattern (shadowSource.substitute "x" "z") =
      applySubst [("x", .fvar "z")] (piToPattern shadowSource) := by
  decide +kernel

def captureSource : Process := .nu "z" (.output "x" "a")

/-- The replacement is absent from the source free names. -/
theorem replacement_not_free_in_source : ("z" : Name) ∉ captureSource.freeNames := by
  intro member
  exact (Finset.mem_sdiff.mp member).2 (Finset.mem_singleton_self "z")

/-- A colliding restriction is freshened, retaining the received free name. -/
theorem capture_substitution_keeps_replacement :
    ("z" : Name) ∈ (captureSource.substitute "x" "z").freeNames := by
  erw [Process.substitute_freeNames_eq]
  refine Finset.mem_image.mpr ⟨"x", ?_, ?_⟩
  · simp [captureSource, Process.freeNames, Name]
  · rfl

/-- Freshening a colliding binder agrees with the locally nameless operation. -/
theorem capture_substitution_agrees_with_pattern :
    piToPattern (captureSource.substitute "x" "z") =
      applySubst [("x", .fvar "z")] (piToPattern captureSource) := by
  decide +kernel

/-- The former result that changed the bound occurrence is rejected. -/
theorem incorrect_shadow_result_rejected :
    shadowSource.substitute "x" "z" ≠ .input "z" "x" (.output "z" "a") := by
  decide +kernel

def disjointBinderSource : Process := .input "a" "b" (.output "x" "b")

/-- A distinct binder gives the same substitution comparison. -/
theorem disjoint_substitution_agrees_with_pattern :
    piToPattern (disjointBinderSource.substitute "x" "z") =
      applySubst [("x", .fvar "z")] (piToPattern disjointBinderSource) := by
  decide +kernel

def nestedBinderSource : Process := .nu "x" (.nu "y" (.output "x" "y"))

def freshenedBinderTarget : Process := .nu "y" (.nu "__" (.output "y" "__"))

def collapsedBinderTarget : Process := .nu "y" (.nu "y" (.output "y" "y"))

/-- Alpha-renaming to an inner binder's name freshens that inner binder. -/
theorem alpha_renames_colliding_inner_binder :
    Nonempty (StructuralCongruence nestedBinderSource freshenedBinderTarget) := by
  have renamed := StructuralCongruence.alpha_nu "x" "y" (.nu "y" (.output "x" "y"))
    (by
      intro member
      exact (Finset.mem_sdiff.mp member).2 (Finset.mem_singleton_self "y"))
  have result : (Process.nu "y" (.output "x" "y")).substitute "x" "y" =
      .nu "__" (.output "y" "__") := by decide +kernel
  rw [result] at renamed
  exact ⟨renamed⟩

/-- The alpha-renamed term keeps the same locally nameless binder incidence. -/
theorem alpha_rename_preserves_pattern :
    piToPattern nestedBinderSource = piToPattern freshenedBinderTarget := by
  decide +kernel

/-- The un-freshened target changes which binder owns the name. -/
theorem unsafe_alpha_target_changes_pattern :
    piToPattern nestedBinderSource ≠ piToPattern collapsedBinderTarget := by
  decide +kernel

/-- An application other than restriction has no authored internal step. -/
theorem piCalc_no_internal_step_from_application (constructor : String) (arguments : List Pattern)
    (notRestriction : constructor ≠ "PiNu") (target : Pattern) :
    ¬ langReduces piCalc (.apply constructor arguments) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    simp only [matchPatternForRule, matchPatternForRuleUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.matchingPresentationForRule?_eq_none_of_no_rules
        (profile := .empty) rfl,
      Mettapedia.OSLF.MeTTaIL.Match.matchPattern]
    <;> simp [Ne.symm notRestriction]

def exchange : Process := .par (.input "a" "x" .nil) (.output "a" "b")

/-- The ordinary named communication is enabled. -/
theorem exchange_handwritten_step : Nonempty (Reduces exchange .nil) := by
  simpa only [Process.substitute_nil] using
    (show Nonempty (Reduces exchange (Process.nil.substitute "x" "b")) from
      ⟨Reduces.comm "a" "x" "b" .nil⟩)

/-- Its encoded COMM redex also runs through the authored engine. -/
theorem exchange_authored_step :
    .collection .hashBag [.apply "PiNil" []] none ∈
      piCalcReducts 1 (piToPattern exchange) := by
  decide +kernel

/-- The named relation explicitly closes communication under restriction. -/
theorem restricted_exchange_handwritten_step :
    Nonempty (Reduces (.nu "r" exchange) (.nu "r" .nil)) :=
  exchange_handwritten_step.map (Reduces.res "r" exchange .nil)

/-- Restriction descent now executes the same exchange in its local context. -/
theorem restricted_exchange_authored_step :
    .apply "PiNu" [.lambda none (.collection .hashBag [.apply "PiNil" []] none)] ∈
      piCalcReducts 2 (piToPattern (.nu "r" exchange)) := by
  decide +kernel

/-- Raw rule results retain their bag or restriction constructor. -/
theorem piCalc_no_internal_step_to_inaction (source : Pattern) :
    ¬ langReduces piCalc source (.apply "PiNil" []) := by
  rintro ⟨fuel, step⟩
  cases step with
  | rule member _ _ target =>
      simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings
          _ _ _ (by decide +kernel)] at target
        simp [Mettapedia.OSLF.MeTTaIL.Match.applyBindings] at target

/-- The raw relation cannot erase the singleton bag of the named COMM result. -/
theorem no_unrestricted_internal_forward_comparison :
    ¬ ∀ (source target : Process), Nonempty (Reduces source target) →
      langReduces piCalc (piToPattern source) (piToPattern target) := by
  intro comparison
  exact piCalc_no_internal_step_to_inaction _
    (comparison _ _ exchange_handwritten_step)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PresentationBoundary
