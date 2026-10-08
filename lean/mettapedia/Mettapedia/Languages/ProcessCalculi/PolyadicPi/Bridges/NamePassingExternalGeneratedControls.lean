import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalDeclaredModel

/-!
# Generated dependent certificates on actual returning compiler executions

A native function type is a primitive parameter domain. The supplied second
component names a finite result type, and the complete-pair motive retains
that component. Its generated branch certificate evaluates to the supplied
section. The real environment-fetch/call example reaches a public rho return
with the generated tree and that checked native value retained in its receipt.

These are native certificate calculations attached to the established guest
program. They do not add natural-number instructions to the guest language.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedControls

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open ContextualSumComprehension NativeLocalTypeOperations NativeLocalSumElimination
open Calculi.NativeDependent
open ExternalPresheafCertificates
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingExternalGeneratedEvidence
open NamePassingEnvironmentControls NamePassingSpineControls
open NamePassingCompilerReadback.Controls
open NamePassingDependentRuntimeControls (startPoint)

noncomputable section

abbrev model := nativeModel ContextCategory
abbrev empty : ContextCategoryᵒᵖ ⥤ Type := model.empty

def naturalFamily (base : ContextCategoryᵒᵖ ⥤ Type) : DisplayedFamily base :=
  (Functor.const base.Elements).obj Nat

def scalar : NativeType empty := LocalType.present (naturalFamily empty)
abbrev scalarBody := scalar.reindex (model.toEmpty ((localModel ContextCategory).ext empty scalar))
noncomputable def functionType : NativeType empty := pi scalar scalarBody
abbrev functionContext : ContextCategoryᵒᵖ ⥤ Type := totalSpace functionType.decoded
def fibre : NativeType functionContext := LocalType.present (naturalFamily functionContext)
abbrev tuple : ContextCategoryᵒᵖ ⥤ Type := tupleContext (C := localModel ContextCategory) functionType fibre

def naturals : ContextCategoryᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def finiteFibre : DisplayedFamily naturals where
  obj point := Fin (Nat.succ point.2)
  map arrow := TypeCat.ofHom (Fin.cast (congrArg (fun value : Nat => value + 1) arrow.property))
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

def tupleName : tuple ⟶ naturals where
  app _ := TypeCat.ofHom fun value => value.2
  naturality := by intros; rfl

def tupleMotive : NativeType tuple := ⟨naturals, finiteFibre, tupleName⟩
noncomputable def motive := tupleMotive.reindex
  (unpack (stableSums ContextCategory) functionType fibre)

theorem motive_on_tuple :
    motive.reindex (pack (stableSums ContextCategory) functionType fibre) = tupleMotive := by
  have comparison : pack (stableSums ContextCategory) functionType fibre ≫
      unpack (stableSums ContextCategory) functionType fibre = 𝟙 tuple :=
    unpack_pack (stableSums ContextCategory) functionType fibre
  change (tupleMotive.reindex (unpack (stableSums ContextCategory) functionType fibre)).reindex
    (pack (stableSums ContextCategory) functionType fibre) = tupleMotive
  rw [← LocalType.reindex_comp]
  exact (congrArg (LocalType.reindex tupleMotive) comparison).trans (LocalType.reindex_id tupleMotive)

def branch : tupleMotive.decoded.sections where
  val point := ⟨point.2.2, Nat.lt_succ_self _⟩
  property := by
    intro first second arrow
    apply Fin.ext
    change first.2.2 = second.2.2
    exact congrArg Sigma.snd arrow.property

noncomputable def pulledBranch :
    (motive.reindex (pack (stableSums ContextCategory) functionType fibre)).decoded.sections :=
  cast (congrArg (fun type : NativeType tuple => (type.decoded.sections : Type))
    motive_on_tuple.symm) branch

noncomputable def declarations :
    External.DeclaredModel.Declarations (C := model)
      (products ContextCategory) (stableSums ContextCategory) where
  scalar := scalar
  fibre := fibre
  motive := motive
  branch := pulledBranch

def identityBody : scalarBody.decoded.sections where
  val point := point.2.2
  property := by
    intro first second arrow
    exact congrArg Sigma.snd arrow.property

noncomputable def identityFunction : functionType.decoded.sections :=
  lam (A := scalar) (B := scalarBody) identityBody

/-- This is a genuine natural map to the two-variable semantic context,
containing a function and the independently supplied second witness. -/
noncomputable def interface (input : Nat) : sourcePrograms ⟶ tuple where
  app world := TypeCat.ofHom fun _ => ⟨⟨PUnit.unit, identityFunction.val ⟨world, PUnit.unit⟩⟩, input⟩
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

noncomputable def interpretation (input : Nat) :
    Interpretation External.Controls.signature (External.Controls.componentContext 0 .nil)
      (External.Controls.fullBranch 0) (External.Controls.signature.termResult .fullBranch) sourcePrograms where
  model := declarations.model
  realization := declarations.realization (products_substitution ContextCategory)
  stable := products_substitution ContextCategory
  beta := products_beta ContextCategory
  eta := NativeLocalPiEta.products_eta ContextCategory
  semanticContext := declarations.componentContext
  semanticType := motive.reindex (pack (stableSums ContextCategory) functionType fibre)
  contextRead := declarations.component_header_read
  typeRead := declarations.branch_result_read (products_substitution ContextCategory)
  interface := interface input

abbrev tree := External.Controls.fullBranchTyped External.Controls.emptyContext

private theorem section_cast_value {A B : DisplayedFamily.{0, 0, 0, 0} tuple}
    (same : A = B) (value : A.sections) (point : tuple.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily.{0, 0, 0, 0} tuple =>
      (family.sections : Type)) same) value).val point) (value.val point) := by
  cases same
  rfl

theorem actual_generated_section (input : Nat) :
    (interpretation input).nativeSection tree = pulledBranch :=
  declarations.branch_section_recovers_supplied (products_substitution ContextCategory)
    (products_beta ContextCategory) (NativeLocalPiEta.products_eta ContextCategory)

theorem generated_value_retains_input (input : Nat) (point : sourcePrograms.Elements) :
    HEq (((interpretation input).valueSection tree).val point)
      (branch.val ((interface input).mapElements.obj point)) := by
  rw [(interpretation input).valueSection_readout, actual_generated_section]
  have same := congrArg LocalType.decoded motive_on_tuple
  exact section_cast_value same.symm branch ((interface input).mapElements.obj point)

theorem dependent_result_fibres (point : sourcePrograms.Elements) :
    tupleMotive.decoded.obj ((interface 0).mapElements.obj point) = Fin 1 ∧
      tupleMotive.decoded.obj ((interface 1).mapElements.obj point) = Fin 2 := ⟨rfl, rfl⟩

theorem erasing_input_changes_value (point : sourcePrograms.Elements) :
    (branch.val ((interface 0).mapElements.obj point)).val ≠
      (branch.val ((interface 1).mapElements.obj point)).val := by
  change (0 : Nat) ≠ 1
  decide

theorem fetched_execution_retains_generated_native_value (input : Nat) :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : GeneratedReceipt (interpretation input) startPoint tree
        (world names) (code start) actual,
      receipt.history.2.tree = tree ∧
        HEq receipt.specification.val.2 (branch.val ((interface input).mapElements.obj startPoint)) ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
        (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt⟩ := retain_generated_prefix (interpretation input) startPoint tree
    (world names) (code start) (supplied start) actual
  exact ⟨final, actual, receipt, receipt.tree_retained,
    receipt.checked_value_retained.trans (generated_value_retains_input input startPoint),
    receipt.public_return_reflected observed, observed⟩

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedControls
