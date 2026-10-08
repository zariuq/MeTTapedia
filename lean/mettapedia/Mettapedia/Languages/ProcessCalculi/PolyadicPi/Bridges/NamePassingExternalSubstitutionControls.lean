import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificateSubstitution
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedControls

/-!
# Varying-input substitution of actual generated native certificates

A natural interface uses its supplied natural-number input as the second
coordinate of the semantic pair context. Pullback along successor changes
the result fibre from Fin 1 to Fin 2 at input zero and changes the checked
value from zero to one. The certificate comparison retains the complete
authored branch derivation. Replacing the successor interface by an erased
input changes its actual value.

The numbers occur in native specifications, not guest instructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalSubstitutionControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers
open Calculi.NativeDependent ExternalPresheafCertificates
open NamePassingDependentEvidence
open NamePassingExternalGeneratedControls

namespace Substitution
open ExternalPresheafCertificateSubstitution

noncomputable section

def varyingInterface : naturals ⟶ tuple where
  app world := TypeCat.ofHom fun input =>
    ⟨⟨PUnit.unit, identityFunction.val ⟨world, PUnit.unit⟩⟩, input⟩
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro input
    apply Sigma.ext
    · apply Sigma.ext
      · rfl
      · exact heq_of_eq (identityFunction.property
          (CategoryOfElements.homMk (F := empty)
            ⟨first, PUnit.unit⟩ ⟨second, PUnit.unit⟩ arrow rfl)).symm
    · rfl

def varyingInterpretation :
    Interpretation External.Controls.signature (External.Controls.componentContext 0 .nil)
      (External.Controls.fullBranch 0) (External.Controls.signature.termResult .fullBranch) naturals where
  model := (interpretation 0).model
  realization := (interpretation 0).realization
  stable := (interpretation 0).stable
  beta := (interpretation 0).beta
  eta := (interpretation 0).eta
  semanticContext := (interpretation 0).semanticContext
  semanticType := (interpretation 0).semanticType
  contextRead := (interpretation 0).contextRead
  typeRead := (interpretation 0).typeRead
  interface := varyingInterface

def successor : naturals ⟶ naturals where
  app _ := TypeCat.ofHom Nat.succ
  naturality := by intros; rfl

def erased : naturals ⟶ naturals where
  app _ := TypeCat.ofHom fun _ : Nat => (0 : Nat)
  naturality := by intros; rfl

private theorem section_cast_readout {A B : DisplayedFamily.{0, 0, 0, 0} tuple}
    (same : A = B) (value : A.sections) (point : tuple.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily.{0, 0, 0, 0} tuple =>
      (family.sections : Type)) same) value).val point) (value.val point) := by
  cases same
  rfl

theorem checked_branch_at_varying_input (point : naturals.Elements) :
    HEq ((varyingInterpretation.valueSection tree).val point)
      (branch.val (varyingInterface.mapElements.obj point)) := by
  rw [varyingInterpretation.valueSection_readout]
  change HEq (((interpretation 0).nativeSection tree).val
    (varyingInterface.mapElements.obj point)) _
  rw [actual_generated_section]
  exact section_cast_readout (congrArg LocalType.decoded motive_on_tuple).symm
    branch (varyingInterface.mapElements.obj point)

theorem substituted_branch_retains_the_actual_input (point : naturals.Elements) :
    HEq (((reindex varyingInterpretation successor).valueSection tree).val point)
      (branch.val (varyingInterface.mapElements.obj (successor.mapElements.obj point))) := by
  rw [valueSection_substitution]
  exact checked_branch_at_varying_input (successor.mapElements.obj point)

theorem successor_changes_result_fibre (world : ContextCategoryᵒᵖ) :
    tupleMotive.decoded.obj (varyingInterface.mapElements.obj ⟨world, (0 : Nat)⟩) = Fin 1 ∧
      tupleMotive.decoded.obj
        (varyingInterface.mapElements.obj (successor.mapElements.obj ⟨world, (0 : Nat)⟩)) = Fin 2 :=
  ⟨rfl, rfl⟩

theorem certificate_comparison_keeps_the_branch_tree (point : naturals.Elements) :
    ((comparison varyingInterpretation successor).hom.app point
      (((reindex varyingInterpretation successor).certificateSection tree).val point)).tree = tree := rfl

theorem certificate_comparison_recovers_checked_value (point : naturals.Elements) :
    HEq (((comparison varyingInterpretation successor).hom.app point
      (((reindex varyingInterpretation successor).certificateSection tree).val point)).value)
      (branch.val (varyingInterface.mapElements.obj (successor.mapElements.obj point))) :=
  substituted_branch_retains_the_actual_input point

theorem erasing_interface_input_changes_the_checked_answer (world : ContextCategoryᵒᵖ) :
    (branch.val (varyingInterface.mapElements.obj (successor.mapElements.obj ⟨world, (0 : Nat)⟩))).val ≠
      (branch.val (varyingInterface.mapElements.obj (erased.mapElements.obj ⟨world, (0 : Nat)⟩))).val := by
  change (1 : Nat) ≠ 0
  exact Nat.one_ne_zero

end
end Substitution
end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalSubstitutionControls
