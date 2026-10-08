import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafComprehensionCertificates
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedLogicalContract

/-!
# Generated comprehension values beside actual compiled prefixes

The full generated native interpretation reads both a domain and its
predicate before constructing the refinement value. The exact compiler
receipt exposes that value through the canonical native decoder. Its
membership is earned by interpretation of the generated comprehension
judgment, and its source tree and origin remain paired with the complete
supplied rho execution prefix.

This is a specification for the initial program interface. It supplies no
dependent guest instruction or evidence action for the current runtime state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedComprehension

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension NativeLocalTypeFormers
open Calculi.NativeDependent RefinementPresheafCertificates
open RefinementPresheafComprehensionCertificates
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative
open NamePassingRefinementGeneratedLogicalContract

variable {S : Refinement.Symbols} {D : Refinement.Signature S} {n : Nat}
variable {context : Refinement.ContextExpr S n} {term : Refinement.TermExpr S n}
variable {domain : Refinement.TypeExpr S n} {predicate : Refinement.PropExpr S (n + 1)}

variable (target : Interpretation D context term (.comprehension domain predicate) compiledPrograms)

local instance semanticCategory : Category target.semanticContext.1.Elements :=
  categoryOfElements (target.semanticContext.1 : ContextCategoryᵒᵖ ⥤ Type)

variable (A : NativeType target.semanticContext.1)
variable (selected : Subfunctor ((Refinement.NativeModel ContextCategory).toCwf.ext
  target.semanticContext.1 A))
variable (domainRead : target.model.evaluateType target.semanticContext domain = some A)
variable (predicateRead : target.model.evaluatePredicate (target.semanticContext.snoc A) predicate = some selected)

variable {point : sourcePrograms.Elements}
variable {tree : Refinement.Derivation D (.term context term (.comprehension domain predicate))}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

noncomputable def selectedSpecification
    (receipt : RuntimeReceipt target point tree world code actual) :
    (PresheafNativePredicateRefinement.displayed A.decoded selected).obj
      (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) :=
  (decoder target A selected domainRead predicateRead).hom.app
    (target.interface.mapElements.obj (compilerMap.mapElements.obj point)) receipt.specification

/-- The current supplied receipt contains genuine membership at its initial
semantic interface, without assuming a predicate-respecting body. -/
theorem selectedSpecification_membership
    (receipt : RuntimeReceipt target point tree world code actual) :
    (⟨(target.interface.mapElements.obj (compilerMap.mapElements.obj point)).2,
      (selectedSpecification target A selected domainRead predicateRead receipt).val⟩ :
        (totalSpace A.decoded).obj point.1) ∈ selected.obj point.1 :=
  (selectedSpecification target A selected domainRead predicateRead receipt).property

theorem selectedSpecification_computes
    (receipt : RuntimeReceipt target point tree world code actual) :
    selectedSpecification target A selected domainRead predicateRead receipt =
      (selectedValueReadout target A selected domainRead predicateRead).app
        (compilerMap.mapElements.obj point)
          ((target.certificateSection tree).val (compilerMap.mapElements.obj point)) := by
  unfold selectedSpecification
  rw [receipt.native_evaluator_value]
  rfl

/-- Certificate readout, native refinement decoding and universal compiler
elimination agree at this exact supplied runtime prefix. -/
theorem certificate_decoder_square
    (receipt : RuntimeReceipt target point tree world code actual) :
    (selectedValueReadout target A selected domainRead predicateRead).app
      (compilerMap.mapElements.obj point)
        ((certificateReadout target).app (compilerMap.mapElements.obj point) receipt.nativeCertificate) =
      selectedSpecification target A selected domainRead predicateRead receipt := by
  change (decoder target A selected domainRead predicateRead).hom.app
    (target.interface.mapElements.obj (compilerMap.mapElements.obj point))
      (((certificateReadout target).app (compilerMap.mapElements.obj point) receipt.nativeCertificate).value) = _
  rw [receipt.target_certificate_value]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementGeneratedComprehension
