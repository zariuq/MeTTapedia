import Mettapedia.OSLF.Framework.WMCalculusNativeObservation

/-!
# A nonconstant context for native WM observations

The WM program object is constant in the constructor stage, but a
generalized program can still depend on a presheaf context. This concrete
Boolean context selects two distinct authored WM state terms. Reindexing by
Boolean negation changes which context point inhabits a native observation.
Thus the substitution action on these predicates is nontrivial, while no
claim about authored binder substitution follows from this example.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeContextExample

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.Framework.WMCalculusSemantics

private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- A context carrying a Boolean choice at every constructor stage. -/
def boolContext : languagePresheafObj wmLanguage :=
  (Functor.const (Opposite (ConstructorObj wmLanguage))).obj Bool

/-- Each Boolean context point selects a different encoded WM state term. -/
def branchProgram : boolContext ⟶ languageProgramObj wmLanguage where
  app _ := TypeCat.ofHom (fun choice : Bool =>
    ULift.up (encodeWM (WMTerm.state (if choice then "on" else "off"))))
  naturality := by
    intro X Y f
    rfl

/-- A nonidentity substitution of the Boolean context. -/
def flipContext : boolContext ⟶ boolContext where
  app _ := TypeCat.ofHom Bool.not
  naturality := by
    intro X Y f
    rfl

/-- A lawful reading whose state observation distinguishes the branches. -/
def booleanReading : WMReading Bool Unit Bool where
  revise := (· || ·)
  extract := fun state _ => state
  combine := (· || ·)
  zero := false
  world := fun name => name == "on"
  query := fun _ => ()

theorem booleanReading_coreLaws : booleanReading.CoreLaws where
  extract_revise := by intro first second query; rfl
  combine_comm := by intro first second; cases first <;> cases second <;> rfl
  combine_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl
  combine_zero := by intro value; cases value <;> rfl

/-- Being the true state is invariant under the reading's state agreement. -/
theorem trueObservation_invariant :
    ObservationInvariant booleanReading .state (fun state => state = true) := by
  intro first second agree observed
  have equal := agree ()
  change first = second at equal
  exact equal ▸ observed

private def stateStage : Opposite (ConstructorObj wmLanguage) :=
  Opposite.op (ConstructorObj.mk ⟨"State", by decide⟩)

/-- The positive context point inhabits the native true-state predicate. -/
theorem branch_true_mem :
    true ∈ (observationInContext booleanReading .state
      (fun state => state = true) boolContext branchProgram).fiber.obj stateStage := by
  change (branchProgram.app stateStage true) ∈
    (observationPredicate booleanReading .state
      (fun state => state = true)).obj stateStage
  exact (observationPredicate_encoded_iff booleanReading .state
    (fun state => state = true) stateStage (.state "on")).2 rfl

/-- The other branch fails the same native observation. -/
theorem branch_false_not_mem :
    false ∉ (observationInContext booleanReading .state
      (fun state => state = true) boolContext branchProgram).fiber.obj stateStage := by
  change ¬ (branchProgram.app stateStage false) ∈
    (observationPredicate booleanReading .state
      (fun state => state = true)).obj stateStage
  intro member
  have false_is_true := (observationPredicate_encoded_iff booleanReading .state
    (fun state => state = true) stateStage (.state "off")).1 member
  cases false_is_true

/-- Reindexing the program by Boolean negation moves the positive point
outside the native true-state predicate. -/
theorem flipped_true_not_mem :
    true ∉ (observationInContext booleanReading .state
      (fun state => state = true) boolContext
      (flipContext ≫ branchProgram)).fiber.obj stateStage := by
  change ¬ (branchProgram.app stateStage false) ∈
    (observationPredicate booleanReading .state
      (fun state => state = true)).obj stateStage
  exact branch_false_not_mem

/-- The context substitution is nontrivial at the predicate level. -/
theorem flip_reindex_changes_observation :
    (observationPredicate booleanReading .state
      (fun state => state = true)).preimage branchProgram ≠
    (observationPredicate booleanReading .state
      (fun state => state = true)).preimage
        (flipContext ≫ branchProgram) := by
  intro equal
  have member := branch_true_mem
  change true ∈ ((observationPredicate booleanReading .state
    (fun state => state = true)).preimage branchProgram).obj stateStage at member
  rw [equal] at member
  exact flipped_true_not_mem member

end Mettapedia.OSLF.Framework.WMCalculusNativeContextExample
