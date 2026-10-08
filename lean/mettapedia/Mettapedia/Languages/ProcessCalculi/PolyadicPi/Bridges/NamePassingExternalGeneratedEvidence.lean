import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificates
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence

/-!
# Checked generated native values through the name-passing compiler

The independent external dependent grammar supplies an authored term
derivation. Its interpretation uses the actual native local-family model,
with successful evaluation derived from the generated rules. A natural
interface map substitutes the semantic variable context at source program
points. Compiler receipts retain the source program, generated tree and
checked native value together. Their universal target readout computes that
same value, and supplied actual rho prefixes retain the execution history.

The interface map is explicit: variable substitution and program-client
plugging are different categories. This theorem attaches checked native
certificates to the compiled program; it does not introduce dependent data
operations into the guest lambda fragment or update initial certificates
to describe the current execution state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal
open Calculi.NativeDependent
open ExternalPresheafCertificates
open NamePassingDependentEvidence NamePassingDependentSpecifications NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative

variable {S : External.Symbols} {D : External.Signature S} {n : Nat}
variable {context : External.ContextExpr S n} {term : External.TermExpr S n}
variable {type : External.TypeExpr S n}

variable (interpretation : Interpretation D context term type sourcePrograms)

local instance semanticCategory : Category interpretation.semanticContext.1.Elements :=
  categoryOfElements (interpretation.semanticContext.1 : ContextCategoryᵒᵖ ⥤ Type)

def specification : DisplayedFamily compiledPrograms :=
  compiledFamily interpretation.valueFamily

def generatedBody : interpretation.certificates ⟶
    reindexDisplayed compilerMap (specification interpretation) :=
  interpretation.valueReadout ≫ carry interpretation.valueFamily

/-- The unique target extension of the checked native value readout. -/
def compiledReadout : compiledFamily interpretation.certificates ⟶
    specification interpretation := realize (generatedBody interpretation)

theorem compiledReadout_computes (point : sourcePrograms.Elements)
    (tree : External.Derivation D (.term context term type)) :
    (compiledReadout interpretation).app (compilerMap.mapElements.obj point)
      ((carry interpretation.certificates).app point
        ((interpretation.certificateSection tree).val point)) =
      (carry interpretation.valueFamily).app point
        ((interpretation.valueSection tree).val point) :=
  realization_computes (generatedBody interpretation) point
    ((interpretation.certificateSection tree).val point)

/-- This readout refers to the actual raw-expression evaluator section,
not to a source success predicate or an arbitrary chosen type inhabitant. -/
theorem compiledReadout_native_value (point : sourcePrograms.Elements)
    (tree : External.Derivation D (.term context term type)) :
    HEq (((compiledReadout interpretation).app (compilerMap.mapElements.obj point)
      ((carry interpretation.certificates).app point
        ((interpretation.certificateSection tree).val point))).val.2)
      ((interpretation.nativeSection tree).val
        (interpretation.interface.mapElements.obj point)) := by
  rw [compiledReadout_computes]
  exact heq_of_eq (interpretation.valueSection_readout tree point)

theorem compiledReadout_unique
    (candidate : compiledFamily interpretation.certificates ⟶ specification interpretation)
    (commutes : carry interpretation.certificates ≫
      (reindexFunctor compilerMap).map candidate = generatedBody interpretation) :
    candidate = compiledReadout interpretation :=
  realization_unique (generatedBody interpretation) candidate commutes

/-- Equal interpreted values do not erase distinct authored certificates. -/
theorem compiled_certificates_injective (point : sourcePrograms.Elements) :
    Function.Injective (fun tree : External.Derivation D (.term context term type) =>
      (carry interpretation.certificates).app point
        ((interpretation.certificateSection tree).val point)) :=
  (carry_injective interpretation.certificates point).comp
    (interpretation.certificateSection_injective point)

abbrev GeneratedReceipt (point : sourcePrograms.Elements)
    (tree : External.Derivation D (.term context term type))
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :=
  Receipt interpretation.certificates (specification interpretation) (generatedBody interpretation)
    point ((interpretation.certificateSection tree).val point) world code actual

/-- The supplied runtime endpoint, reflected source history, retained
proof tree and checked semantic value occur in one actual execution receipt. -/
theorem retain_generated_prefix (point : sourcePrograms.Elements)
    (tree : External.Derivation D (.term context term type))
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero
      world.world = some code) {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    Nonempty (GeneratedReceipt interpretation point tree world code actual) :=
  retain_prefix interpretation.certificates (specification interpretation)
    (generatedBody interpretation) point ((interpretation.certificateSection tree).val point)
    world code compiled actual

variable {interpretation}
variable {point : sourcePrograms.Elements}
variable {tree : External.Derivation D (.term context term type)}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

theorem GeneratedReceipt.tree_retained
    (receipt : GeneratedReceipt interpretation point tree world code actual) :
    receipt.history.2.tree = tree := rfl

theorem GeneratedReceipt.checked_value_retained
    (receipt : GeneratedReceipt interpretation point tree world code actual) :
    HEq receipt.specification.val.2 ((interpretation.nativeSection tree).val
      (interpretation.interface.mapElements.obj point)) := by
  rw [receipt.computed]
  exact heq_of_eq (interpretation.valueSection_readout tree point)

theorem GeneratedReceipt.generated_evaluator_readout
    (receipt : GeneratedReceipt interpretation point tree world code actual) :
    interpretation.model.evaluateTerm interpretation.semanticContext term =
      some ⟨interpretation.semanticType, interpretation.nativeSection receipt.history.2.tree⟩ :=
  tree.termSection_readout interpretation.model interpretation.realization
    interpretation.stable interpretation.beta interpretation.eta interpretation.semanticContext
    interpretation.semanticType interpretation.contextRead interpretation.typeRead

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingExternalGeneratedEvidence
