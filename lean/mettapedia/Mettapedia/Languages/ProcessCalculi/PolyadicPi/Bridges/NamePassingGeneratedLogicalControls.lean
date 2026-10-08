import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedLogicalContract
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedControls

/-!
# Generated target specifications on a real returning compiler execution

The target interface supplies a native function and an independent witness.
Its complete generated branch has a genuinely dependent finite result
type. Substitution along the compiler is the authored source interface,
and the unique target readout returns the same checked value on an actual
rho execution. Erasing the witness changes that value and its result fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedLogicalControls

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers
open Calculi.NativeDependent ExternalPresheafCertificates
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingGeneratedLogicalContract
open NamePassingExternalGeneratedControls
open NamePassingEnvironmentControls NamePassingSpineControls
open NamePassingCompilerReadback.Controls
open NamePassingDependentRuntimeControls (startPoint)

noncomputable section

def targetInterface (input : Nat) : compiledPrograms ⟶ tuple where
  app world := TypeCat.ofHom fun _ =>
    ⟨⟨PUnit.unit, identityFunction.val ⟨world, PUnit.unit⟩⟩, input⟩
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro program
    apply Sigma.ext
    · apply Sigma.ext
      · rfl
      · exact heq_of_eq (identityFunction.property
          (CategoryOfElements.homMk (F := empty)
            ⟨first, PUnit.unit⟩ ⟨second, PUnit.unit⟩ arrow rfl)).symm
    · rfl

def targetInterpretation (input : Nat) :
    Interpretation External.Controls.signature (External.Controls.componentContext 0 .nil)
      (External.Controls.fullBranch 0) (External.Controls.signature.termResult .fullBranch)
      compiledPrograms where
  model := (interpretation input).model
  realization := (interpretation input).realization
  stable := (interpretation input).stable
  beta := (interpretation input).beta
  eta := (interpretation input).eta
  semanticContext := (interpretation input).semanticContext
  semanticType := (interpretation input).semanticType
  contextRead := (interpretation input).contextRead
  typeRead := (interpretation input).typeRead
  interface := targetInterface input

theorem source_interface_commutes (input : Nat) :
    compilerMap ≫ targetInterface input = interface input := by
  apply NatTrans.ext
  funext world
  rfl

theorem generated_target_section (input : Nat) :
    (targetInterpretation input).nativeSection tree = pulledBranch :=
  actual_generated_section input

private theorem cast_value {A B : DisplayedFamily.{0, 0, 0, 0} tuple}
    (same : A = B) (value : A.sections) (point : tuple.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily.{0, 0, 0, 0} tuple =>
      (family.sections : Type)) same) value).val point) (value.val point) := by
  cases same
  rfl

theorem target_value_is_the_checked_branch (input : Nat) (point : compiledPrograms.Elements) :
    HEq (((targetInterpretation input).valueSection tree).val point)
      (branch.val ((targetInterface input).mapElements.obj point)) := by
  rw [(targetInterpretation input).valueSection_readout, generated_target_section]
  exact cast_value (congrArg LocalType.decoded motive_on_tuple).symm branch
    ((targetInterface input).mapElements.obj point)

theorem actual_compiler_readout (input : Nat) (point : sourcePrograms.Elements) :
    HEq ((valueReadout (targetInterpretation input)).app (compilerMap.mapElements.obj point)
      ((carry (source (targetInterpretation input)).certificates).app point
        (((source (targetInterpretation input)).certificateSection tree).val point)))
      (branch.val ((targetInterface input).mapElements.obj (compilerMap.mapElements.obj point))) := by
  rw [valueReadout_computes]
  exact target_value_is_the_checked_branch input (compilerMap.mapElements.obj point)

theorem target_specification_retains_both_fibres (point : compiledPrograms.Elements) :
    tupleMotive.decoded.obj ((targetInterface 0).mapElements.obj point) = Fin 1 ∧
      tupleMotive.decoded.obj ((targetInterface 1).mapElements.obj point) = Fin 2 := ⟨rfl, rfl⟩

theorem erasing_target_witness_changes_the_answer (point : compiledPrograms.Elements) :
    (branch.val ((targetInterface 1).mapElements.obj point)).val ≠
      (branch.val ((targetInterface 0).mapElements.obj point)).val := by
  change (1 : Nat) ≠ 0
  exact Nat.one_ne_zero

theorem actual_return_retains_the_target_certificate (input : Nat) :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : RuntimeReceipt (targetInterpretation input) startPoint tree
        (world names) (code start) actual,
      receipt.history.2.tree = tree ∧ receipt.nativeCertificate.val.1 = startPoint.2 ∧
        HEq receipt.specification
          (branch.val ((targetInterface input).mapElements.obj
            (compilerMap.mapElements.obj startPoint))) ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
        (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt⟩ := retain_runtime_prefix (targetInterpretation input) startPoint tree
    (world names) (code start) (supplied start) actual
  have value : HEq receipt.specification
      (branch.val ((targetInterface input).mapElements.obj
        (compilerMap.mapElements.obj startPoint))) := by
    rw [receipt.computed]
    exact target_value_is_the_checked_branch input (compilerMap.mapElements.obj startPoint)
  exact ⟨final, actual, receipt, receipt.tree_retained, receipt.origin_retained, value,
    receipt.public_return_reflected observed, observed⟩

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedLogicalControls
