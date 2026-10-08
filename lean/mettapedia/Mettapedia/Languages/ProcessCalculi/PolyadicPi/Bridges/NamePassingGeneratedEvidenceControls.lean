import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls
import Mettapedia.TypeTheory.Calculi.NativeDependent.RuleInitiality
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.BoundedNaturalModel

/-!
# Generated dependent certificates on a supplied returning rho execution

The certificate is a generated native function application. Its interpretation
computes an input n in Fin (n + 1), using the actual native Pi operation. The
same receipt retains a supplied returning compiler execution and its exact
endpoint. Two declarations with equal interpreted values retain distinct
authored certificates through this compiler.

This joins native proof interpretation and actual program execution; it
does not add natural-number data to the compiled lambda source language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedEvidenceControls

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open JudgmentDerivation DisplayedPresheafTransport DisplayedPresheafComprehension
open NamePassingGeneratedEvidence NamePassingDependentEvidence
open NamePassingDependentRuntimeEvidence NamePassingDependentRuntimeControls
open NamePassingSpineControls
open NamePassingCompilerReadback.Controls
open Calculi.NativeDependent
open Calculi.NativeDependent.Examples.BoundedNaturalModel Calculi.NativeDependent.RuleInitiality
open Calculi.NativeDependent.PresheafInterpretation

abbrev nativeObjects := objects ContextCategory
abbrev nativeConstants := constants ContextCategory
abbrev nativePredicates := predicates ContextCategory
noncomputable abbrev nativeDeclarations : ∀ {n : Nat} {formula : Formula Nat PUnit n},
    Primitive n formula → (family nativeObjects nativeConstants nativePredicates formula).sections :=
  declarations ContextCategory
abbrev nativePoint := point ContextCategory startPoint.1

noncomputable def targetAlgebra : Algebra (signature Primitive) :=
  nativeAlgebra Primitive nativeObjects nativeConstants nativePredicates nativeDeclarations

/-- The control's local model uses the actual dependent native function
carrier and the independently supplied primitive meanings. -/
noncomputable def models : compiledPrograms.Elements ⥤ Algebra (signature Primitive) :=
  (Functor.const _).obj targetAlgebra

abbrev applicationTree (number : Nat) :
    Derivation (signature Primitive)
      ⟨0, .substitute input (ObjectSubstitution.instantiate (.constant number))⟩ :=
  encode Primitive (applicationProof number)

theorem interpreted_application (number : Nat) :
    interpret targetAlgebra (applicationTree number) =
      proof nativeObjects nativeConstants nativePredicates nativeDeclarations
        (applicationProof number) :=
  native_interpreter_agreement Primitive nativeObjects nativeConstants nativePredicates
    nativeDeclarations _

/-- Generated proof evaluation computes after genuine receipt elimination
at the actual compiled source component. -/
theorem compiled_application_computes (number : Nat) :
    ((compiledReadout models _).app (compilerMap.mapElements.obj startPoint)
      ((carry (certificates _)).app startPoint (applicationTree number))).val nativePoint =
        (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) := by
  rw [compiledReadout_computes models startPoint (applicationTree number)]
  change (interpret targetAlgebra (applicationTree number)).val nativePoint = _
  rw [interpreted_application]
  exact application_computes ContextCategory startPoint.1 number

/-- The native calculation and the actual returning rho path occur in
one receipt, retaining its supplied proof tree and exact observed endpoint. -/
theorem returning_execution_with_generated_certificate (number : Nat) :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target
        (process start) final,
      ∃ receipt : GeneratedReceipt models startPoint (applicationTree number)
          (world names) (code start) actual,
        receipt.history.2 = applicationTree number ∧
          receipt.specification.val nativePoint =
            (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) ∧
          (RhoUnaryInputObservation.targetPredicate
            (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt⟩ := retain_generated_prefix models startPoint (applicationTree number)
    (world names) (code start) (supplied start) actual
  refine ⟨final, actual, receipt, receipt.tree_retained, ?_, observed⟩
  rw [receipt.interprets]
  change (interpret targetAlgebra (applicationTree number)).val nativePoint = _
  rw [interpreted_application]
  exact application_computes ContextCategory startPoint.1 number

abbrev originTree (number : Nat) (origin : Bool) :
    Derivation (signature Primitive)
      ⟨0, .substitute input (ObjectSubstitution.instantiate (.constant number))⟩ :=
  encode Primitive (Proof.declaration (Primitive.closed number origin))

theorem origin_trees_distinct (number : Nat) : originTree number false ≠ originTree number true := by
  intro same
  have decoded := congrArg (decode Primitive) same
  rw [decode_encode, decode_encode] at decoded
  exact declaration_origins_distinct number decoded

theorem compiled_origin_receipts_distinct (number : Nat) :
    (carry (certificates _)).app startPoint (originTree number false) ≠
      (carry (certificates _)).app startPoint (originTree number true) :=
  fun same => origin_trees_distinct number (carry_injective _ startPoint same)

/-- Value equality in the actual native model does not justify erasure
of the compiler receipt's different supplied declaration origins. -/
theorem compiled_values_forget_origins (number : Nat) :
    (compiledReadout models _).app (compilerMap.mapElements.obj startPoint)
        ((carry (certificates _)).app startPoint (originTree number false)) =
      (compiledReadout models _).app (compilerMap.mapElements.obj startPoint)
        ((carry (certificates _)).app startPoint (originTree number true)) := by
  rw [compiledReadout_computes models startPoint (originTree number false),
    compiledReadout_computes models startPoint (originTree number true)]
  change interpret targetAlgebra (originTree number false) =
    interpret targetAlgebra (originTree number true)
  exact (native_interpreter_agreement Primitive nativeObjects nativeConstants nativePredicates
    nativeDeclarations
    (Proof.declaration (Primitive.closed number false))).trans
      ((declaration_values_agree ContextCategory number).trans
        (native_interpreter_agreement Primitive nativeObjects nativeConstants nativePredicates
          nativeDeclarations
          (Proof.declaration (Primitive.closed number true))).symm)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedEvidenceControls
