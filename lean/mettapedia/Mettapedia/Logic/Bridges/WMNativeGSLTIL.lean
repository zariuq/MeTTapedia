import Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
import Mettapedia.GSLT.ReproducibleBuild.GSLTIL

/-!
# Exact WM answers across the native and relational boundaries

The WM reading's semantic extraction graph is also a proof-family relation
in GSLT-IL. Its evidence is an explicit checked answer receipt. The relation
earns a functional companion because extraction supplies a total and unique
answer, while arbitrary GSLT-IL routes retain their relational meaning.

The receipt here certifies extensional answer equality; it does not contain
an inference derivation, a source occurrence, or an execution trace.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMNativeGSLTIL

open _root_.CategoryTheory
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ReproducibleBuild.GSLTIL
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.GSLT.RelationPresentation

/-- A checked extensional answer to one state-query request. This is a
dependent witness family, but not a provenance or derivation receipt. -/
structure AnswerReceipt {State Query V : Type}
    (R : WMReading State Query V) (request : State × Query) (answer : V) : Type where
  checked : R.extract request.1 request.2 = answer

/-- An answer receipt has no derivation multiplicity: its sole field is an
equality proof. Operational proof histories require a different fibre. -/
theorem answerReceipt_subsingleton {State Query V : Type}
    (R : WMReading State Query V) (request : State × Query) (answer : V) :
    Subsingleton (AnswerReceipt R request answer) := by
  constructor
  intro first second
  cases first
  cases second
  rfl

/-- The WM query graph as a GSLT-IL semantic relation, retaining its answer
receipt in every fibre. -/
def answerRelation {State Query V : Type}
    (R : WMReading State Query V) : Mettapedia.GSLT.RelationPresentation.Rel (State × Query) V where
  evidence request answer := AnswerReceipt R request answer

/-- Native graph membership and nonempty relational answer evidence agree
exactly at the same state, query, and evidence value. -/
theorem receipt_iff_nativeGraph {State Query V : Type}
    (R : WMReading State Query V)
    (X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      (Mettapedia.OSLF.Framework.WMCalculusContextClosure.wmExtVertexLanguageDefWithCong
        Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)))
    (state : State) (query : Query) (value : V) :
    Nonempty ((answerRelation R).evidence (state, query) value) ↔
      ((state, query), value) ∈ (evidenceGraph R).obj X := by
  constructor
  · rintro ⟨receipt⟩
    exact (evidenceGraph_mem_iff R X state query value).2 receipt.checked
  · intro graphMember
    exact ⟨⟨(evidenceGraph_mem_iff R X state query value).1 graphMember⟩⟩

/-- The functional licence is proved fibrewise from the receipt equation;
the answer relation is not defined by aliasing a function companion. -/
def answerRepresentation {State Query V : Type}
    (R : WMReading State Query V) :
    Mettapedia.GSLT.RelationPresentation.Rel.Representation (answerRelation R) where
  map request := R.extract request.1 request.2
  exact request answer :=
    { toFun := fun receipt => ⟨⟨receipt.checked⟩⟩
      invFun := fun equality => ⟨equality.down.down⟩
      left_inv := by intro receipt; cases receipt; rfl
      right_inv := by
        intro equality
        exact (instSubsingletonEqWitness _ _).allEq _ _ }

/-- GSLT-IL's represented-map authority selects actual extraction. -/
theorem answerRepresentation_map {State Query V : Type}
    (R : WMReading State Query V) (request : State × Query) :
    (answerRepresentation R).map request =
      R.extract request.1 request.2 :=
  rfl

/-- The relational build has the same checked evidence fibre as the native
graph, without turning unrelated routes into functions. -/
theorem answerBuild_receipt {State Query V : Type}
    (R : WMReading State Query V) (request : State × Query) (answer : V) :
    (relationBuild (answerRelation R)) request answer =
      AnswerReceipt R request answer :=
  rfl

/-- Any selected artifact observation of the represented WM answer build is
reproducible by the established relational-build theorem. -/
theorem answerBuild_reproducible {State Query V : Type}
    (R : WMReading State Query V)
    (observation :
      Mettapedia.GSLT.Core.ReproducibleBuild.ArtifactObservation V) :
    Mettapedia.GSLT.Core.ReproducibleBuild.Reproducible
      (relationBuild (answerRelation R)) observation :=
  represented_reproducible (answerRepresentation R) observation

/-! ## Syntax-to-answer chaining with its retained middle value -/

/-- A checked interpretation of a pair of typed WM terms as a semantic
state-query request. -/
structure TermPairReceipt {State Query V : Type}
    (R : WMReading State Query V)
    (terms : WMTerm .state × WMTerm .query)
    (request : State × Query) : Type where
  checked : (R.denote terms.1, R.denote terms.2) = request

/-- The first GSLT-IL leg interprets WM syntax but retains the semantic
pair and an explicit checked witness. -/
def termPairRelation {State Query V : Type}
    (R : WMReading State Query V) :
    Mettapedia.GSLT.RelationPresentation.Rel (WMTerm .state × WMTerm .query) (State × Query) where
  evidence terms request := TermPairReceipt R terms request

/-- Typed-term interpretation earns a functional companion because
denotation selects exactly one semantic pair. -/
def termPairRepresentation {State Query V : Type}
    (R : WMReading State Query V) :
    Mettapedia.GSLT.RelationPresentation.Rel.Representation (termPairRelation R) where
  map terms := (R.denote terms.1, R.denote terms.2)
  exact terms request :=
    { toFun := fun receipt => ⟨⟨receipt.checked⟩⟩
      invFun := fun equality => ⟨equality.down.down⟩
      left_inv := by intro receipt; cases receipt; rfl
      right_inv := by
        intro equality
        exact (instSubsingletonEqWitness _ _).allEq _ _ }

/-- The actual two-stage answer relation keeps the intermediate state-query
pair, its denotation witness, and its checked answer receipt. -/
def termAnswerChain {State Query V : Type}
    (R : WMReading State Query V) :
    Mettapedia.GSLT.RelationPresentation.Rel (WMTerm .state × WMTerm .query) V :=
  Mettapedia.GSLT.RelationPresentation.Rel.Chain (termPairRelation R) (answerRelation R)

/-- The proof-relevant chain is functional only because both constituent
relations have independently earned representations. -/
def termAnswerChainRepresentation {State Query V : Type}
    (R : WMReading State Query V) :
    Mettapedia.GSLT.RelationPresentation.Rel.Representation (termAnswerChain R) :=
  Mettapedia.GSLT.RelationPresentation.Rel.chainRepresentation (termPairRepresentation R)
    (answerRepresentation R)

/-- The represented map of the chain agrees with the WM calculus's
`Extract` denotation, while the chain's evidence still retains the middle
state-query pair. -/
theorem termAnswerChain_map_eq_denote_extract {State Query V : Type}
    (R : WMReading State Query V)
    (terms : WMTerm .state × WMTerm .query) :
    (termAnswerChainRepresentation R).map terms =
      R.denote (.extract terms.1 terms.2) :=
  rfl

/-- A chain fibre is inhabited exactly for the semantic WM answer. This
support theorem does not discard the richer chained witness type. -/
theorem termAnswerChain_nonempty_iff {State Query V : Type}
    (R : WMReading State Query V)
    (terms : WMTerm .state × WMTerm .query) (value : V) :
    Nonempty ((termAnswerChain R).evidence terms value) ↔
      R.denote (.extract terms.1 terms.2) = value := by
  constructor
  · rintro ⟨⟨request, pairReceipt, answerReceipt⟩⟩
    cases pairReceipt.checked
    exact answerReceipt.checked
  · intro equal
    exact ⟨⟨(R.denote terms.1, R.denote terms.2), ⟨rfl⟩, ⟨equal⟩⟩⟩

/-- The complete extensional chain has at most one witness at any fixed
answer. It retains its semantic middle object structurally but cannot be
mistaken for an occurrence-sensitive derivation trace. -/
theorem termAnswerChain_evidence_subsingleton {State Query V : Type}
    (R : WMReading State Query V)
    (terms : WMTerm .state × WMTerm .query) (value : V) :
    Subsingleton ((termAnswerChain R).evidence terms value) := by
  have deterministic :=
    (termAnswerChainRepresentation R).deterministic terms
  constructor
  intro first second
  have equal :
      (⟨value, first⟩ : Sigma fun answer =>
        (termAnswerChain R).evidence terms answer) =
      ⟨value, second⟩ :=
    deterministic.allEq _ _
  cases equal
  rfl

end Mettapedia.Logic.Bridges.WMNativeGSLTIL
