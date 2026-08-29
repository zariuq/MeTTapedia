import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Mettapedia.GSLT.Dynamics.WorldOfViews
import Mettapedia.GSLT.ReproducibleBuild.GSLTIL

/-!
# Dynamic-link provenance over open relational GSLT-IL routes

Runtime tool coupling needs machine-readable provenance without pretending
that interoperability creates one global artifact, one functional translator,
or a legal conclusion.  This module layers ordered link histories over the
existing proof-relevant semantic relations used by GSLT-IL.

Route composition retains the intermediate endpoint and both witnesses in the
underlying relation, while the provenance history concatenates the two link
histories.  Link identities, sources, and licensing metadata remain available
to downstream reasoning.  Missing links are observable.

The legal boundary is stated negatively and narrowly.  Metadata supplies an
input to adjudication; without an additional legal rule, it does not determine
derivative-work status or force copyleft propagation across a protocol
boundary.  The countermodel below is a logical non-entailment result, not a
claim about the outcome of any real dispute.

Relational transport remains primary.  A direct function is exposed only by
the existing total, proof-relevantly deterministic representation certificate.
Likewise, a family of local provenance ledgers becomes global only when a
separate gluing witness exists.

References:

- M. Hatta, *Reproducibility Is the New Copyleft: Defining AGI-Oriented
  Reproducible Builds* (2026), Section 8.3.
- L. Torres-Arias et al., *in-toto: Providing Farm-to-Table Guarantees for
  Bits and Bytes* (2019), for authenticated supply-chain links.
- V. Veitas and D. Weinbaum, *A World of Views* (2014), for relationally open
  plural systems.

The GSLT-IL provenance decoration, its composition laws, and the technical/
legal non-entailment controls are new.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ReproducibleBuild.GSLTIL
open Mettapedia.GSLT.WorldOfViews
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RelationalInternalLanguage

universe u

/-! ## Machine-readable link metadata -/

/-- Metadata for one runtime or build-time route link.  The type parameters
keep identifiers policy-neutral; no stringly typed registry is assumed. -/
structure LinkMetadata
    (LinkId ToolId Revision SourceId LicenseId : Type u) where
  link : LinkId
  tool : ToolId
  revision : Revision
  sources : Multiset SourceId
  licenses : Multiset LicenseId
  deriving DecidableEq

namespace History

variable {LinkId ToolId Revision SourceId LicenseId : Type u}

/-- Ordered link identities in a provenance history. -/
def linkIds
    (history : List (LinkMetadata LinkId ToolId Revision SourceId LicenseId)) :
    List LinkId :=
  history.map LinkMetadata.link

/-- Source occurrences retained across all links. -/
def sources :
    List (LinkMetadata LinkId ToolId Revision SourceId LicenseId) ->
      Multiset SourceId
  | [] => 0
  | link :: rest => link.sources + sources rest

/-- Licensing metadata retained across all links.  Repeated declarations stay
repeated occurrences. -/
def licenses :
    List (LinkMetadata LinkId ToolId Revision SourceId LicenseId) ->
      Multiset LicenseId
  | [] => 0
  | link :: rest => link.licenses + licenses rest

@[simp] theorem linkIds_append
    (left right :
      List (LinkMetadata LinkId ToolId Revision SourceId LicenseId)) :
    linkIds (left ++ right) = linkIds left ++ linkIds right := by
  simp [linkIds]

@[simp] theorem sources_append
    (left right :
      List (LinkMetadata LinkId ToolId Revision SourceId LicenseId)) :
    sources (left ++ right) = sources left + sources right := by
  induction left with
  | nil => simp [sources]
  | cons link rest ih =>
      simp [sources, ih, add_assoc]

@[simp] theorem licenses_append
    (left right :
      List (LinkMetadata LinkId ToolId Revision SourceId LicenseId)) :
    licenses (left ++ right) = licenses left + licenses right := by
  induction left with
  | nil => simp [licenses]
  | cons link rest ih =>
      simp [licenses, ih, add_assoc]

/-- A history covers a declared link scope when every required identity occurs
in the ordered ledger. -/
def Covers
    (history : List (LinkMetadata LinkId ToolId Revision SourceId LicenseId))
    (required : Set LinkId) : Prop :=
  forall link, required link -> link ∈ linkIds history

/-- Coverage composes across concatenated histories and unioned requirements. -/
theorem covers_append_union
    {left right :
      List (LinkMetadata LinkId ToolId Revision SourceId LicenseId)}
    {first second : Set LinkId}
    (leftCovers : Covers left first) (rightCovers : Covers right second) :
    Covers (left ++ right) (first ∪ second) := by
  intro link required
  rw [linkIds_append, List.mem_append]
  rcases required with firstRequired | secondRequired
  · exact Or.inl (leftCovers link firstRequired)
  · exact Or.inr (rightCovers link secondRequired)

end History

/-! ## Provenance-decorated semantic relations -/

/-- A GSLT-IL semantic relation together with the exact ordered provenance of
each proof-relevant route witness. -/
structure ProvenancedRelation
    (Source Target Metadata : Type u) where
  relation : Semantic.Rel Source Target
  provenance : forall {source target},
    relation.evidence source target -> List Metadata

namespace ProvenancedRelation

variable {First Middle Last Metadata : Type u}

/-- Forget metadata only after retaining the original GSLT-IL relation. -/
def underlyingBuild (route : ProvenancedRelation First Middle Metadata) :=
  relationBuild route.relation

/-- Relational route composition concatenates the histories attached to the
two retained evidence witnesses. -/
def Chain
    (earlier : ProvenancedRelation First Middle Metadata)
    (later : ProvenancedRelation Middle Last Metadata) :
    ProvenancedRelation First Last Metadata where
  relation := Semantic.Rel.Chain earlier.relation later.relation
  provenance witness :=
    earlier.provenance witness.2.1 ++ later.provenance witness.2.2

@[simp] theorem chain_relation
    (earlier : ProvenancedRelation First Middle Metadata)
    (later : ProvenancedRelation Middle Last Metadata) :
    (Chain earlier later).relation =
      Semantic.Rel.Chain earlier.relation later.relation :=
  rfl

@[simp] theorem chain_provenance
    (earlier : ProvenancedRelation First Middle Metadata)
    (later : ProvenancedRelation Middle Last Metadata)
    {source : First} {target : Last}
    (witness : (Chain earlier later).relation.evidence source target) :
    (Chain earlier later).provenance witness =
      earlier.provenance witness.2.1 ++ later.provenance witness.2.2 :=
  rfl

/-- A direct graph with one declared history. -/
def graph {Source Target : Type u} (map : Source -> Target)
    (history : List Metadata) : ProvenancedRelation Source Target Metadata where
  relation := Semantic.Rel.graph map
  provenance _ := history

/-- Exact functional transport is inherited only from representation
certificates for both component relations. -/
def chainRepresentation
    {earlier : ProvenancedRelation First Middle Metadata}
    {later : ProvenancedRelation Middle Last Metadata}
    (earlierRepresentation : Semantic.Rel.Representation earlier.relation)
    (laterRepresentation : Semantic.Rel.Representation later.relation) :
    Semantic.Rel.Representation (Chain earlier later).relation :=
  Representation.horizontalComp earlierRepresentation laterRepresentation

end ProvenancedRelation

/-! ## Technical metadata does not contain a legal rule -/

/-- An artifact paired with technical provenance and a separately supplied
external adjudication.  The last field is deliberately not computed from the
metadata. -/
structure AdjudicatedArtifact
    (Artifact Metadata Adjudication : Type u) where
  artifact : Artifact
  provenance : List Metadata
  adjudication : Adjudication

namespace AdjudicatedArtifact

variable {Artifact Metadata Adjudication : Type u}

/-- The complete technical view available to downstream tooling. -/
def technicalView
    (artifact : AdjudicatedArtifact Artifact Metadata Adjudication) :
    Artifact × List Metadata :=
  (artifact.artifact, artifact.provenance)

/-- Technical metadata determines an adjudication only when the adjudication
is constant on every fibre of the technical view. -/
def MetadataDeterminesAdjudication : Prop :=
  Function.FactorsThrough
    (fun artifact : AdjudicatedArtifact Artifact Metadata Adjudication =>
      artifact.adjudication)
    technicalView

end AdjudicatedArtifact

/-! ## Controls -/

namespace Canary

inductive LinkId where
  | compile
  | invoke
deriving DecidableEq, Repr

inductive ToolId where
  | compiler
  | runtimeTool
deriving DecidableEq, Repr

inductive SourceId where
  | sourceTree
  | toolResponse
deriving DecidableEq, Repr

inductive LicenseId where
  | copyleft
  | permissive
deriving DecidableEq, Repr

abbrev Metadata := LinkMetadata LinkId ToolId Nat SourceId LicenseId

def compileMetadata : Metadata where
  link := .compile
  tool := .compiler
  revision := 7
  sources := {.sourceTree}
  licenses := {.copyleft}

def invocationMetadata : Metadata where
  link := .invoke
  tool := .runtimeTool
  revision := 11
  sources := {.toolResponse}
  licenses := {.permissive}

def compileRoute : ProvenancedRelation Unit Unit Metadata :=
  ProvenancedRelation.graph id [compileMetadata]

def invocationRoute : ProvenancedRelation Unit Unit Metadata :=
  ProvenancedRelation.graph id [invocationMetadata]

/-- Same runtime relation as `invocationRoute`, but with the invocation link
omitted from its ledger. -/
def missingInvocationRoute : ProvenancedRelation Unit Unit Metadata :=
  ProvenancedRelation.graph id []

def identityEvidence : (Semantic.Rel.graph (id : Unit -> Unit)).evidence () () :=
  ⟨⟨rfl⟩⟩

def completeChain := ProvenancedRelation.Chain compileRoute invocationRoute

def missingLinkChain :=
  ProvenancedRelation.Chain compileRoute missingInvocationRoute

def completeChainWitness : completeChain.relation.evidence () () :=
  ⟨(), identityEvidence, identityEvidence⟩

def missingLinkChainWitness : missingLinkChain.relation.evidence () () :=
  ⟨(), identityEvidence, identityEvidence⟩

@[simp] theorem completeChain_history :
    completeChain.provenance completeChainWitness =
      [compileMetadata, invocationMetadata] :=
  rfl

@[simp] theorem missingLinkChain_history :
    missingLinkChain.provenance missingLinkChainWitness = [compileMetadata] :=
  rfl

def bothLinks : Set LinkId := Set.univ

theorem completeChain_covers_bothLinks :
    History.Covers (completeChain.provenance completeChainWitness) bothLinks := by
  intro link _required
  cases link <;>
    simp [History.linkIds, compileMetadata, invocationMetadata]

/-- Omitting a route ledger entry is observable even though execution remains
available. -/
theorem missingLinkChain_not_complete :
    Not (History.Covers
      (missingLinkChain.provenance missingLinkChainWitness) bothLinks) := by
  intro covers
  have invokeRequired : bothLinks LinkId.invoke :=
    Set.mem_univ LinkId.invoke
  have invokeCovered := covers LinkId.invoke invokeRequired
  simp [History.linkIds, compileMetadata] at invokeCovered

/-- The complete route exposes both licensing declarations to downstream
reasoning, with order and multiplicity retained. -/
theorem completeChain_licenses :
    History.licenses (completeChain.provenance completeChainWitness) =
      ({LicenseId.copyleft, LicenseId.permissive} : Multiset LicenseId) := by
  decide

/-- The complete and missing-link routes have definitionally the same GSLT-IL
relation and hence the same possible endpoint artifacts. -/
theorem same_relation_different_provenance :
    completeChain.relation = missingLinkChain.relation /\
      completeChain.provenance completeChainWitness !=
        missingLinkChain.provenance missingLinkChainWitness := by
  constructor
  · rfl
  · decide

def compileRepresentation : Semantic.Rel.Representation compileRoute.relation :=
  Semantic.Rel.graphRepresentation id

def invocationRepresentation :
    Semantic.Rel.Representation invocationRoute.relation :=
  Semantic.Rel.graphRepresentation id

/-- Functional composition is available for the exact graph routes because
both carry explicit representation certificates. -/
def completeChainRepresentation :
    Semantic.Rel.Representation completeChain.relation :=
  ProvenancedRelation.chainRepresentation compileRepresentation
    invocationRepresentation

def choiceRoute : ProvenancedRelation Unit Bool Metadata where
  relation := Semantic.Canary.choice
  provenance _ := [invocationMetadata]

/-- Machine-readable provenance does not turn an open nondeterministic route
into a function. -/
theorem choiceRoute_not_functional :
    Not (Nonempty (Semantic.Rel.Representation choiceRoute.relation)) :=
  Semantic.Canary.choice_not_representable

/-! ### Legal non-entailment -/

inductive ProtocolAdjudication where
  | propagationApplies
  | separateAdjudicationRequired
deriving DecidableEq, Repr

abbrev LegalCase :=
  AdjudicatedArtifact Unit Metadata ProtocolAdjudication

def propagationCase : LegalCase where
  artifact := ()
  provenance := [compileMetadata, invocationMetadata]
  adjudication := .propagationApplies

def separateReviewCase : LegalCase where
  artifact := ()
  provenance := [compileMetadata, invocationMetadata]
  adjudication := .separateAdjudicationRequired

theorem legalCases_same_technical_view :
    propagationCase.technicalView = separateReviewCase.technicalView :=
  rfl

/-- Identical artifacts and metadata do not determine an externally supplied
legal adjudication without an additional legal rule. -/
theorem metadata_does_not_determine_adjudication :
    Not
      (AdjudicatedArtifact.MetadataDeterminesAdjudication
        (Artifact := Unit) (Metadata := Metadata)
        (Adjudication := ProtocolAdjudication)) := by
  intro determines
  have equal := determines legalCases_same_technical_view
  exact ProtocolAdjudication.noConfusion equal

/-- A copyleft declaration in a protocol ledger is compatible with a case
requiring separate adjudication.  This is a logical independence witness, not
a legal ruling. -/
theorem copyleft_metadata_does_not_force_protocol_propagation :
    Not (forall legalCase : LegalCase,
      LicenseId.copyleft ∈ History.licenses legalCase.provenance ->
      legalCase.adjudication = ProtocolAdjudication.propagationApplies) := by
  intro forces
  have propagated := forces separateReviewCase (by
    simp [separateReviewCase, History.licenses, compileMetadata])
  exact ProtocolAdjudication.noConfusion propagated

/-! ### Relational interoperability does not imply global ledger gluing -/

inductive LedgerView where
  | client
  | provider
deriving DecidableEq, Repr

def ledgerModular : ModularView (List Metadata) where
  Module := Unit
  module_nonempty := ⟨()⟩
  LocalState _ := List Metadata
  observer _ := ⟨id⟩
  jointlyFaithful := by
    intro first second same
    exact congrFun same ()

def ledgerSystem : System LedgerView where
  State _ := List Metadata
  modular _ := ledgerModular
  relation _ _ _ _ := Unit

theorem ledgerSystem_isOpen : ledgerSystem.IsOpen := by
  intro source target different
  exact ⟨⟨[], [], ()⟩⟩

/-- A proposed global ledger must restrict to exactly the same history at both
local views. -/
def singleLedgerGluing : GluingProblem ledgerSystem where
  Global := List Metadata
  restrict history _ := history

def splitLedgerFamily : (view : LedgerView) -> ledgerSystem.State view
  | .client => [compileMetadata]
  | .provider => [invocationMetadata]

theorem splitLedgerFamily_coordinates :
    ledgerSystem.CanCoordinate .client .provider :=
  ⟨⟨splitLedgerFamily .client, splitLedgerFamily .provider, ()⟩⟩

/-- Runtime coordination between the local views does not fabricate a single
global provenance ledger. -/
theorem splitLedgerFamily_not_gluable :
    Not (singleLedgerGluing.Realizes splitLedgerFamily) := by
  rintro ⟨global, realizes⟩
  have client := realizes LedgerView.client
  have provider := realizes LedgerView.provider
  have equal : [compileMetadata] = [invocationMetadata] := by
    exact client.symm.trans provider
  have links := congrArg (List.map LinkMetadata.link) equal
  simp [compileMetadata, invocationMetadata] at links

def consistentLedgerFamily : (view : LedgerView) -> ledgerSystem.State view :=
  fun _ => [compileMetadata, invocationMetadata]

/-- Global provenance is available when an explicit gluing witness is
supplied. -/
theorem consistentLedgerFamily_gluable :
    singleLedgerGluing.Realizes consistentLedgerFamily := by
  exact ⟨[compileMetadata, invocationMetadata], fun view => rfl⟩

end Canary

end Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance

#print axioms Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance.History.covers_append_union
#print axioms Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance.ProvenancedRelation.chainRepresentation
#print axioms Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance.Canary.same_relation_different_provenance
#print axioms Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance.Canary.metadata_does_not_determine_adjudication
#print axioms Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance.Canary.choiceRoute_not_functional
#print axioms Mettapedia.GSLT.ReproducibleBuild.DynamicLinkProvenance.Canary.splitLedgerFamily_not_gluable
