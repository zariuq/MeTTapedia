import Mettapedia.Computability.FragmentwiseComputationalTrinityExactness
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareOSLFSemantics

/-!
# Declaration-aware Prime computational-trinity calibration

This module is a deliberately bounded calibration, not the final Prime
computational-trinity crown.  It connects three real carriers over one
constant context:

* an occurrence-indexed run of the authored formed-typing proof search;
* its retained logical derivation; and
* the intrinsic contextual term constructed by the independent semantics.

The comparison proves that the current calculus-to-OSLF-to-contextual-term
route inhabits the generic trinity interface.  It also records a load-bearing
limitation: erasing the run occurrence is sound and complete at the logical
derivation level but not faithful.  Consequently theoremhood agreement cannot
be promoted to an exact computational trinity.

The context is constant only to isolate this proof-identity boundary.  A final
Prime crown must replace it with the actual formed-context category and prove
naturality under typed substitution; this file does not claim that result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace DeclarationAwareComputationalTrinityCalibration

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinityExactness
open DeclarationAwareFormedTyping
open DeclarationAwareOSLFSemantics
open DeclarationAwareStructuralTyping

abbrev Context := CategoryTheory.Discrete PUnit

private def here : Contextᵒᵖ :=
  Opposite.op (CategoryTheory.Discrete.mk PUnit.unit)

/-! ## The three concrete carriers -/

/-- A logical element is a retained derivation of one complete formed-typing
query in the authored declaration-aware calculus. -/
abbrev LogicalAt (query : FormedTypingQuery) :=
  Derivation formedTypingExtension.target (encodeFormedTypingQuery query)

/-- A program element additionally retains the identity of this execution
occurrence.  Equal derivation trees used at distinct occurrences remain
distinct programs. -/
def ProgramCarrier :=
  Σ query : FormedTypingQuery, Nat × LogicalAt query

/-- The logical face retains the complete authored derivation tree but forgets
which execution occurrence submitted it. -/
def LogicCarrier :=
  Σ query : FormedTypingQuery, LogicalAt query

/-- The spatial face contains the actual displayed contextual term constructed
from the independent intrinsic semantics. -/
def SpaceCarrier :=
  Σ query : FormedTypingQuery,
    DeclarationAwareOSLFSemantics.Formed.IntrinsicTermWitness query

def programFace : Face Context :=
  (CategoryTheory.Functor.const Contextᵒᵖ).obj ProgramCarrier

def logicFace : Face Context :=
  (CategoryTheory.Functor.const Contextᵒᵖ).obj LogicCarrier

def spaceFace : Face Context :=
  (CategoryTheory.Functor.const Contextᵒᵖ).obj SpaceCarrier

/-! ## Authored run, logical proof, and contextual realization -/

/-- Forget only the external run occurrence, retaining the exact query and
derivation tree. -/
def forgetOccurrence : ProgramCarrier → LogicCarrier :=
  fun run ↦ ⟨run.1, run.2.2⟩

/-- Every retained derivation executes as a proof-search path from its
singleton obligation to the empty obligation list. -/
def proofSearchTrace (run : ProgramCarrier) :
    (proofSearchGSLT formedTypingExtension.target).MultiStep
      [encodeFormedTypingQuery run.1] [] :=
  derivationToProofSearch run.2.2

/-- Interpret an authored logical derivation in the independent intrinsic
formed-typing semantics and construct its displayed contextual term. -/
noncomputable def realizeLogical : LogicCarrier → SpaceCarrier
  | ⟨query, derivation⟩ =>
      let meaning := formedTypingSemanticExtension.interpret derivation
      let evidence : IntrinsicFormedTyping query := meaning.2 query rfl
      ⟨query, ⟨evidence, evidence.term evidence.nativeGoal⟩⟩

def programToLogic : programFace ⟶ logicFace :=
  (CategoryTheory.Functor.const Contextᵒᵖ).map
    (TypeCat.ofHom forgetOccurrence)

noncomputable def logicToSpace : logicFace ⟶ spaceFace :=
  (CategoryTheory.Functor.const Contextᵒᵖ).map
    (TypeCat.ofHom realizeLogical)

/-- The direct realization is definitionally the composite, so the trinity
triangle commutes without installing an additional semantic authority. -/
noncomputable def comparison : Comparison Context where
  program := programFace
  logic := logicFace
  space := spaceFace
  programToLogic := programToLogic
  logicToSpace := logicToSpace
  programToSpace := CategoryTheory.CategoryStruct.comp
    programToLogic logicToSpace
  coherence := rfl

/-- All three carriers form a sound forward fragment.  This says every
retained run has a logical derivation and every derivation constructs a
contextual term; it does not assert reflection or global equivalence. -/
noncomputable def totalFragments :
    ComputationalTrinity.FragmentwiseComparison comparison where
  programFragment := Constraint.total comparison.program
  logicFragment := Constraint.total comparison.logic
  spaceFragment := Constraint.total comparison.space
  programLogicCompatible := by
    intro context logical represented
    trivial
  logicSpaceCompatible := by
    intro context spatial represented
    trivial

/-- The generic commuting-triangle theorem applies to the actual
declaration-aware route. -/
theorem every_run_constructs_a_spatial_point :
    ((Constraint.total comparison.program).pushforward
      comparison.programToSpace).Entails
        (Constraint.total comparison.space) :=
  totalFragments.programSpaceCompatible

/-! ## Exact OSLF and spatial readouts -/

/-- The logical carrier at a query is inhabited exactly when the generated
OSLF reachability type is satisfied. -/
theorem oslf_iff_logical_inhabited (query : FormedTypingQuery) :
    (gsltOSLF (proofSearchGSLT formedTypingExtension.target)).satisfies
        [encodeFormedTypingQuery query]
        (derivableNativeType formedTypingExtension.target).pred ↔
      Nonempty (LogicalAt query) :=
  satisfies_derivableNativeType_iff_derivation
    formedTypingExtension.target (encodeFormedTypingQuery query)

/-- Spatial realization retains the exact source query. -/
@[simp] theorem realizeLogical_query (logical : LogicCarrier) :
    (realizeLogical logical).1 = logical.1 := by
  cases logical
  rfl

/-- The generalized element constructed in the spatial face has exactly the
authored subject code of its query. -/
theorem realizeLogical_term_code (logical : LogicCarrier) :
    (realizeLogical logical).2.2.code = logical.1.subject := by
  cases logical with
  | mk query derivation =>
      simp [realizeLogical, IntrinsicFormedTyping.nativeGoal]

/-! ## A concrete dependent-function run -/

open DeclarationAwareFormedTyping.Examples

/-- Reconstruct the typed derivation whose erasure is the accepted generated
proof for the binder-sensitive dependent-function specimen. -/
noncomputable def simplePiDerivation : LogicalAt simplePiQuery :=
  Classical.choose
    ((G2_checkRaw_iff_exists_derivation_erases_to).mp
      simplePi_derived_raw_accepted)

noncomputable def simplePiRun (occurrence : Nat) : ProgramCarrier :=
  ⟨simplePiQuery, (occurrence, simplePiDerivation)⟩

noncomputable def simplePiLogical : LogicCarrier :=
  ⟨simplePiQuery, simplePiDerivation⟩

noncomputable def simplePiSpatial : SpaceCarrier :=
  realizeLogical simplePiLogical

@[simp] theorem simplePi_run_forgets_to_same_logic (occurrence : Nat) :
    forgetOccurrence (simplePiRun occurrence) = simplePiLogical :=
  rfl

theorem simplePi_spatial_term_code :
    simplePiSpatial.2.2.code = simplePi := by
  simpa [simplePiSpatial, simplePiLogical, simplePiQuery] using
    realizeLogical_term_code simplePiLogical

/-! ## Soundness and completeness do not imply faithfulness -/

/-- Forgetting occurrence is sound on the complete selected carriers. -/
theorem programLogic_sound :
    ((Constraint.total comparison.program).pushforward
      comparison.programToLogic).Entails
        (Constraint.total comparison.logic) := by
  intro context logical represented
  trivial

/-- Every retained logical derivation has an occurrence-indexed operational
representative. -/
theorem programLogic_complete :
    (Constraint.total comparison.logic).Entails
      ((Constraint.total comparison.program).pushforward
        comparison.programToLogic) := by
  intro context logical admitted
  refine ⟨⟨logical.1, (0, logical.2)⟩, trivial, ?_⟩
  rfl

/-- Distinct executions of the same proof map to the same logical and spatial
elements. -/
theorem comparison_loses_run_occurrence :
    comparison.LosesProgramInformation := by
  refine ⟨here, simplePiRun 0, simplePiRun 1, ?_, rfl⟩
  intro equality
  have occurrenceEquality := congrArg (fun run : ProgramCarrier ↦ run.2.1)
    equality
  simp [simplePiRun] at occurrenceEquality

/-- The program-to-logic leg is not exact on the complete carriers even though
it is sound and complete there: faithfulness is the missing property. -/
theorem no_total_programLogic_exact :
    ¬ Nonempty
      (ExactBridge comparison.programToLogic
        (Constraint.total comparison.program)
        (Constraint.total comparison.logic)) := by
  rintro ⟨bridge⟩
  have equalRuns : simplePiRun 0 = simplePiRun 1 :=
    bridge.faithful here trivial trivial rfl
  have occurrenceEquality := congrArg (fun run : ProgramCarrier ↦ run.2.1)
    equalRuns
  simp [simplePiRun] at occurrenceEquality

/-- This is the concrete Prime instance of the generic non-collapse law. -/
theorem programLogic_sound_complete_but_not_exact :
    ((Constraint.total comparison.program).pushforward
        comparison.programToLogic).Entails
          (Constraint.total comparison.logic) ∧
      (Constraint.total comparison.logic).Entails
        ((Constraint.total comparison.program).pushforward
          comparison.programToLogic) ∧
      ¬ Nonempty
        (ExactBridge comparison.programToLogic
          (Constraint.total comparison.program)
          (Constraint.total comparison.logic)) :=
  ⟨programLogic_sound, programLogic_complete,
    no_total_programLogic_exact⟩

#print axioms proofSearchTrace
#print axioms every_run_constructs_a_spatial_point
#print axioms oslf_iff_logical_inhabited
#print axioms realizeLogical_term_code
#print axioms simplePi_spatial_term_code
#print axioms comparison_loses_run_occurrence
#print axioms programLogic_sound_complete_but_not_exact

end DeclarationAwareComputationalTrinityCalibration
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
