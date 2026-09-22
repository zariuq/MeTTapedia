import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism
import Mettapedia.GSLT.ReproducibleBuild.GSLTIL

/-!
# Dependent total receipt sections and relational representability

The observable receipt family is genuinely partial. Its dependent product
over every observable request has a term exactly when the matching semantic
GSLT-IL relation admits a total functional representation. This is a
semantic-request result; quantifying only over authored terms would not cover
requests outside the denotation of those terms. A second dependent product
over authored requests has its own exact representability criterion; a
Boolean control proves that the global and authored criteria differ.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability

open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
open Mettapedia.GSLT.RelationPresentation
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusNativeContextExample
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism
open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.ReproducibleBuild.GSLTIL

variable {State Query V : Type} {R : WMReading State Query V}

/-- A dependent product in the staged families semantic families CwF: for
every observable state-query request, produce its checked actual answer. -/
def allObservableReceiptPi (capability : WMCapability R) :
    familiesCwF.Ty (mode := stageOfNat 0) PUnit :=
  familiesCwF.pi (mode := stageOfNat 0)
    (fun _ => observableRequestContext R)
    (fun extension =>
      ObservableReceipt capability extension.2
        (extractObs R extension.2.1 extension.2.2))

/-- A section of this dependent product is exactly total capability support
over observable requests. The answer equality is then supplied by actual
extraction, not by a default for unsupported inputs. -/
theorem allObservableReceiptPi_iff_allObservableSupport
    (capability : WMCapability R) :
    Nonempty (allObservableReceiptPi capability PUnit.unit) ↔
      ∀ request : observableRequestContext R,
        observableSupport capability request.1 request.2 := by
  constructor
  · rintro ⟨receiptSection⟩ request
    exact (receiptSection request).supported
  · intro supported
    exact ⟨fun request => ⟨supported request, rfl⟩⟩

/-- Observational quotienting does not hide an unsupported semantic request:
every quotient class has a raw representative, and capability support
respects the reading's state observations. -/
theorem allObservableSupport_iff_allRawSupport
    (capability : WMCapability R) :
    (∀ request : observableRequestContext R,
      observableSupport capability request.1 request.2) ↔
      ∀ request : State × Query,
        capability.supports request.1 request.2 := by
  constructor
  · intro supported request
    exact (observableSupport_classOf capability request.1 request.2).mp
      (supported (classOf R request.1, request.2))
  · intro supported request
    rcases request with ⟨classState, query⟩
    induction classState using Quotient.inductionOn with
    | h state =>
        exact (observableSupport_classOf capability state query).mpr
          (supported (state, query))

/-- A native dependent total-answer term exists exactly when the semantic
GSLT-IL capability relation is representable by a total function. The
equivalence uses the quotient coverage theorem above and the independently
proved relational representability criterion. -/
theorem receiptPi_iff_semanticRepresentation
    (capability : WMCapability R) :
    Nonempty (allObservableReceiptPi capability PUnit.unit) ↔
      Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
        (capabilityAnswerRelation capability)) := by
  rw [allObservableReceiptPi_iff_allObservableSupport]
  exact (allObservableSupport_iff_allRawSupport capability).trans
    (representable_iff_all_supported capability).symm

/-- A checked dependent total-answer term supplies the exact functional
licence needed by the existing GSLT-IL reproducible-build theorem. The
result is about the semantic capability relation and a selected observation
of its answer, not an executable compiler for authored syntax. -/
theorem receiptPi_implies_reproducible
    (capability : WMCapability R)
    (totalReceipt : allObservableReceiptPi capability PUnit.unit)
    (observation : ArtifactObservation V) :
    Reproducible (relationBuild (capabilityAnswerRelation capability))
      observation := by
  obtain ⟨representation⟩ :=
    (receiptPi_iff_semanticRepresentation capability).mp ⟨totalReceipt⟩
  exact represented_reproducible representation observation

/-! ## The weaker authored-request boundary -/

/-- The checked syntax-to-capability chain retains one semantic middle
request, but that request and its answer are uniquely determined by the
authored terms. Its proof-relevant fibres are therefore deterministic even
when capability support is partial. -/
theorem termCapabilityChain_deterministic
    (capability : WMCapability R) :
    Mettapedia.GSLT.LooseRelationEquipment.Deterministic
      (termCapabilityChain capability).toLoose := by
  intro terms
  constructor
  rintro ⟨firstAnswer, firstRequest, firstPair, firstReceipt⟩
    ⟨secondAnswer, secondRequest, secondPair, secondReceipt⟩
  cases firstPair.checked
  cases secondPair.checked
  cases firstReceipt.checked
  cases secondReceipt.checked
  have pairEq : firstPair = secondPair := by
    cases firstPair
    cases secondPair
    rfl
  have receiptEq : firstReceipt = secondReceipt := by
    cases firstReceipt
    cases secondReceipt
    rfl
  cases pairEq
  cases receiptEq
  rfl

/-- The authored-term chain earns a functional GSLT-IL representation
exactly when every request denoted by an authored pair is supported. This is
weaker than totality on all semantic requests unless syntax names them all. -/
theorem termCapabilityChain_representable_iff_namedSupport
    (capability : WMCapability R) :
    Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation (termCapabilityChain capability)) ↔
      ∀ terms : WMTerm .state × WMTerm .query,
        capability.supports (R.denote terms.1) (R.denote terms.2) := by
  rw [Mettapedia.GSLT.RelationPresentation.Rel.representable_iff_total_and_deterministic]
  constructor
  · intro represented terms
    exact (termCapabilityChain_has_answer_iff capability terms).mp
      (represented.1 terms)
  · intro namedSupport
    refine ⟨?_, termCapabilityChain_deterministic capability⟩
    intro terms
    exact (termCapabilityChain_has_answer_iff capability terms).mpr
      (namedSupport terms)

/-- Prime's semantic families CwF can also form the dependent receipt
product only over requests named by typed WM terms. This is the pullback of
the observable receipt family along authored-term denotation. -/
def allAuthoredReceiptPi (capability : WMCapability R) :
    familiesCwF.Ty (mode := stageOfNat 0) PUnit :=
  familiesCwF.pi (mode := stageOfNat 0)
    (fun _ => WMTerm .state × WMTerm .query)
    (fun extension =>
      ObservableReceipt capability
        (classOf R (R.denote extension.2.1), R.denote extension.2.2)
        (R.extract (R.denote extension.2.1) (R.denote extension.2.2)))

/-- Restrict a globally supported dependent receipt section along the
authored-term denotation map. The converse requires every semantic request
to be denotable or otherwise supported. -/
def restrictTotalReceipt (capability : WMCapability R)
    (total : allObservableReceiptPi capability PUnit.unit) :
    allAuthoredReceiptPi capability PUnit.unit :=
  fun terms => total
    (classOf R (R.denote terms.1), R.denote terms.2)

/-- A term of the authored-request Pi-type is exactly support on all
denotable requests. Unlike the semantic-request Pi-type, it says nothing
about semantic states or queries that the syntax does not name. -/
theorem allAuthoredReceiptPi_iff_namedSupport
    (capability : WMCapability R) :
    Nonempty (allAuthoredReceiptPi capability PUnit.unit) ↔
      ∀ terms : WMTerm .state × WMTerm .query,
        capability.supports (R.denote terms.1) (R.denote terms.2) := by
  constructor
  · rintro ⟨receiptSection⟩ terms
    exact (observableSupport_classOf capability _ _).mp
      (receiptSection terms).supported
  · intro namedSupport
    exact ⟨fun terms =>
      ⟨(observableSupport_classOf capability _ _).mpr (namedSupport terms), rfl⟩⟩

/-- The authored dependent receipt product earns exactly the functional
license for the authored GSLT-IL chain, with its intermediate semantic
request still present in each relation witness. -/
theorem authoredReceiptPi_iff_termChainRepresentation
    (capability : WMCapability R) :
    Nonempty (allAuthoredReceiptPi capability PUnit.unit) ↔
      Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation (termCapabilityChain capability)) :=
  (allAuthoredReceiptPi_iff_namedSupport capability).trans
    (termCapabilityChain_representable_iff_namedSupport capability).symm

/-! A strict control: syntax can name only a supported state while the
semantic carrier still contains an unsupported state. -/

def namedTrueReading : WMReading Bool Unit Bool :=
  { booleanReading with world := fun _ => true }

theorem namedTrueReading_coreLaws : namedTrueReading.CoreLaws where
  extract_revise := booleanReading_coreLaws.extract_revise
  combine_comm := booleanReading_coreLaws.combine_comm
  combine_assoc := booleanReading_coreLaws.combine_assoc
  combine_zero := booleanReading_coreLaws.combine_zero

def namedTrueCapability : WMCapability namedTrueReading where
  supports := fun state _ => state = true
  respectsAgree := by
    intro first second query agree
    have equal := agree ()
    change first = second at equal
    subst second
    exact Iff.rfl

theorem namedTrueReading_denote_state : (term : WMTerm .state) →
    namedTrueReading.denote term = true
  | .state _ => rfl
  | .revise first second => by
      change (namedTrueReading.denote first || namedTrueReading.denote second) = true
      rw [namedTrueReading_denote_state first, namedTrueReading_denote_state second]
      rfl

theorem namedTrue_no_false_state_term :
    ¬ ∃ term : WMTerm .state, namedTrueReading.denote term = false := by
  rintro ⟨term, falseDenotation⟩
  rw [namedTrueReading_denote_state term] at falseDenotation
  cases falseDenotation

/-- Every authored request is supported, so the authored receipt Pi-type
and the authored chain representation are inhabited. -/
theorem namedTrue_authored_receiptPi_inhabited :
    Nonempty (allAuthoredReceiptPi namedTrueCapability PUnit.unit) := by
  apply (allAuthoredReceiptPi_iff_namedSupport namedTrueCapability).mpr
  intro terms
  exact namedTrueReading_denote_state terms.1

theorem namedTrue_termChain_representable :
    Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (termCapabilityChain namedTrueCapability)) :=
  (authoredReceiptPi_iff_termChainRepresentation namedTrueCapability).mp
    namedTrue_authored_receiptPi_inhabited

/-- The same capability is not total on all semantic requests: `false`
exists as a state but no authored state term denotes it. -/
theorem namedTrue_semantic_receiptPi_empty :
    ¬ Nonempty (allObservableReceiptPi namedTrueCapability PUnit.unit) := by
  intro total
  have supported := (allObservableSupport_iff_allRawSupport namedTrueCapability).mp
    ((allObservableReceiptPi_iff_allObservableSupport namedTrueCapability).mp total)
  have impossible := supported (false, ())
  exact Bool.false_ne_true impossible

theorem namedTrue_authored_not_semantic_total :
    Nonempty (allAuthoredReceiptPi namedTrueCapability PUnit.unit) ∧
      ¬ Nonempty (allObservableReceiptPi namedTrueCapability PUnit.unit) :=
  ⟨namedTrue_authored_receiptPi_inhabited,
    namedTrue_semantic_receiptPi_empty⟩

/-- The Boolean capability with an unsupported false request has no
dependent total-answer term: the Π-type does not manufacture a default. -/
theorem truthCapability_receiptPi_empty :
    ¬ Nonempty (allObservableReceiptPi
      Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample.truthCapability
      PUnit.unit) := by
  intro receiptSection
  exact Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL.truthCapability_not_representable
    ((receiptPi_iff_semanticRepresentation _).mp receiptSection)

/-- The same Boolean reading with total support has a dependent term for
every observable request. -/
theorem allBooleanCapability_receiptPi_inhabited :
    Nonempty (allObservableReceiptPi allBooleanCapability PUnit.unit) := by
  apply (allObservableReceiptPi_iff_allObservableSupport _).mpr
  intro request
  rcases request with ⟨classState, query⟩
  induction classState using Quotient.inductionOn with
  | h state =>
      exact (observableSupport_classOf allBooleanCapability state query).mpr trivial

/-- Widening capability support can create a total Π-section; the forward
backend map does not reflect totality back to its source. -/
theorem widening_creates_total_receipt_section :
    Nonempty (allObservableReceiptPi allBooleanCapability PUnit.unit) ∧
    ¬ Nonempty (allObservableReceiptPi
      Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample.truthCapability
      PUnit.unit) :=
  ⟨allBooleanCapability_receiptPi_inhabited,
    truthCapability_receiptPi_empty⟩

/-- A real total Boolean capability consequently yields a reproducible
semantic GSLT-IL build even at exact answer identity. -/
theorem allBooleanCapability_reproducible_identity :
    Reproducible
      (relationBuild (capabilityAnswerRelation allBooleanCapability))
      (ArtifactObservation.identity Bool) := by
  obtain ⟨totalReceipt⟩ := allBooleanCapability_receiptPi_inhabited
  exact receiptPi_implies_reproducible allBooleanCapability totalReceipt
    (ArtifactObservation.identity Bool)

end Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability
