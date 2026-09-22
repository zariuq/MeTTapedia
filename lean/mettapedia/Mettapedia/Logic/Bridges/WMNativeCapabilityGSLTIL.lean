import Mettapedia.Logic.Bridges.WMNativeGSLTIL
import Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample

/-!
# Partial WM capabilities in the relational internal language

An unsupported WM request has no answer receipt, even though the underlying
reading has a total extraction function. The capability relation is therefore
representable by a total function exactly when every request is supported.
This keeps the supported-query predicate in the proof-relevant interpretation
instead of silently returning an answer for an unsupported query.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL

open _root_.CategoryTheory
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.RelationPresentation
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample
open Mettapedia.OSLF.Framework.WMCalculusNativeContextExample
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.Logic.Bridges.WMNativeGSLTIL

/-- A supported request with its checked extensional answer. The support
proof remains in the fibre; it is not a derivation or occurrence trace. -/
structure CapabilityAnswerReceipt {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (request : State × Query) (answer : V) : Type where
  supported : capability.supports request.1 request.2
  checked : R.extract request.1 request.2 = answer

/-- Unsupported requests have no receipt at any putative answer. -/
theorem no_receipt_of_unsupported {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (request : State × Query)
    (unsupported : ¬ capability.supports request.1 request.2)
    (answer : V) :
    ¬ Nonempty (CapabilityAnswerReceipt capability request answer) := by
  rintro ⟨receipt⟩
  exact unsupported receipt.supported

/-- The admitted WM answers form a relation, not a total map. -/
def capabilityAnswerRelation {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Mettapedia.GSLT.RelationPresentation.Rel (State × Query) V where
  evidence request answer := CapabilityAnswerReceipt capability request answer

/-- Relational evidence and native supported-graph membership agree on each
state, query, and answer, with no invented default outside the graph. -/
theorem receipt_iff_supportedGraph {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      (Mettapedia.OSLF.Framework.WMCalculusContextClosure.wmExtVertexLanguageDefWithCong
        Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)))
    (state : State) (query : Query) (answer : V) :
    Nonempty ((capabilityAnswerRelation capability).evidence (state, query) answer) ↔
      ((state, query), answer) ∈ (supportedGraph capability).obj X := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receipt.supported, receipt.checked⟩
  · rintro ⟨supported, checked⟩
    exact ⟨⟨supported, checked⟩⟩

/-- A request has some relational answer exactly when it is supported. -/
theorem has_answer_iff_supported {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (request : State × Query) :
    Nonempty (Sigma fun answer =>
      (capabilityAnswerRelation capability).evidence request answer) ↔
        capability.supports request.1 request.2 := by
  constructor
  · rintro ⟨⟨answer, receipt⟩⟩
    exact receipt.supported
  · intro supported
    exact ⟨⟨R.extract request.1 request.2, ⟨supported, rfl⟩⟩⟩

private theorem receipt_subsingleton {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (request : State × Query) (answer : V) :
    Subsingleton (CapabilityAnswerReceipt capability request answer) := by
  constructor
  intro first second
  cases first
  cases second
  congr

/-- All requests must be supported before the partial relation earns a
total GSLT-IL functional representation. The converse is constructive from
the reading's actual extraction function. -/
theorem representable_iff_all_supported {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation (capabilityAnswerRelation capability)) ↔
      ∀ request : State × Query,
        capability.supports request.1 request.2 := by
  constructor
  · rintro ⟨representation⟩ request
    exact (has_answer_iff_supported capability request).1
      (representation.total request)
  · intro allSupported
    refine ⟨{
      map := fun request => R.extract request.1 request.2
      exact := fun request answer =>
        { toFun := fun receipt => ⟨⟨receipt.checked⟩⟩
          invFun := fun equality =>
            ⟨allSupported request, equality.down.down⟩
          left_inv := by
            intro receipt
            exact (receipt_subsingleton capability request answer).allEq _ _
          right_inv := by
            intro equality
            exact (instSubsingletonEqWitness _ _).allEq _ _ }
    }⟩

/-- A concrete proper capability lacks a global compiler-function licence:
the false Boolean request is unsupported, although true has an answer. -/
theorem truthCapability_not_representable :
    ¬ Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (capabilityAnswerRelation truthCapability)) := by
  intro represented
  have allSupported :=
    (representable_iff_all_supported truthCapability).1 represented
  have impossible := allSupported (false, ())
  exact (by simp [truthCapability] at impossible : False)

/-- The positive control: its true request has the extracted Boolean answer. -/
theorem truthCapability_true_receipt :
    Nonempty ((capabilityAnswerRelation truthCapability).evidence
      (true, ()) true) := by
  exact ⟨⟨rfl, rfl⟩⟩

/-! ## Authored WM terms retain their semantic middle request -/

/-- The partial syntax-to-answer route preserves the denoted request, its
interpretation receipt, and its supported-answer receipt. -/
def termCapabilityChain {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Mettapedia.GSLT.RelationPresentation.Rel (WMTerm .state × WMTerm .query) V :=
  Mettapedia.GSLT.RelationPresentation.Rel.Chain (termPairRelation R) (capabilityAnswerRelation capability)

/-- A typed pair of WM terms has an admitted answer precisely when its
denoted request is supported. The existential keeps the intermediate
semantic request and both witnesses inside the relation fibre. -/
theorem termCapabilityChain_has_answer_iff {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (terms : WMTerm .state × WMTerm .query) :
    Nonempty (Sigma fun answer =>
      (termCapabilityChain capability).evidence terms answer) ↔
        capability.supports (R.denote terms.1) (R.denote terms.2) := by
  constructor
  · rintro ⟨⟨answer, request, pairReceipt, answerReceipt⟩⟩
    cases pairReceipt.checked
    exact answerReceipt.supported
  · intro supported
    exact ⟨⟨R.extract (R.denote terms.1) (R.denote terms.2),
      ⟨(R.denote terms.1, R.denote terms.2), ⟨rfl⟩,
        ⟨supported, rfl⟩⟩⟩⟩

/-- An unsupported *denotable* request defeats a total functional
representation even after passing through the syntax interpretation leg. -/
theorem termCapabilityChain_not_representable_of_unsupported {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (terms : WMTerm .state × WMTerm .query)
    (unsupported :
      ¬ capability.supports (R.denote terms.1) (R.denote terms.2)) :
    ¬ Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (termCapabilityChain capability)) := by
  rintro ⟨representation⟩
  exact unsupported
    ((termCapabilityChain_has_answer_iff capability terms).1
      (representation.total terms))

/-- The Boolean false-state atom names a genuinely unsupported request,
so the partial relation does not become total by restricting to authored WM
terms. -/
theorem truthCapability_termChain_not_representable :
    ¬ Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (termCapabilityChain truthCapability)) := by
  apply termCapabilityChain_not_representable_of_unsupported truthCapability
    (.state "off", .query "available")
  simp [truthCapability, booleanReading, WMReading.denote]

/-- Conversely, the Boolean true-state atom has a concrete supported
syntax-to-answer route. -/
theorem truthCapability_termChain_positive :
    Nonempty ((termCapabilityChain truthCapability).evidence
      (.state "on", .query "available") true) := by
  exact ⟨⟨(true, ()), ⟨by decide⟩, ⟨rfl, rfl⟩⟩⟩

end Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
