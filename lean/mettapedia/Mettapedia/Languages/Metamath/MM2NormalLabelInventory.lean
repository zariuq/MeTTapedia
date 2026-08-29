import Mettapedia.GSLT.Core.FiniteOccurrenceLookup
import Mettapedia.Languages.Metamath.MM2DataEncoding

/-!
# Source-derived finite label inventories for normal Metamath proofs

A normal proof token may name either an active hypothesis or an already
admitted assertion.  This module turns that exact source-owned finite scope
into occurrence-indexed passive MM2 rows.  The proof token is not consulted:
the source transformation publishes the searchable inventory, while the
verifier performs lookup and decides whether a submitted token is present.

The typed inventory is reified through the generic finite-occurrence
transformation before it is encoded as MM2 atoms.  Thus the executable rows
are driven by the GSLT data transformation rather than by a fixture name or a
host-side proof lookup.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalLabelInventory

open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.GSLT.LinkedInventoryLoader
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTState

/-- Which source-owned lookup table licenses a normal proof label. -/
inductive NormalLabelKind where
  | hypothesis
  | assertion
deriving DecidableEq, Repr

def normalLabelKindAtom : NormalLabelKind → Atom
  | .hypothesis => .symbol "mm-normal-label-hypothesis"
  | .assertion => .symbol "mm-normal-label-assertion"

def normalLabelEntryAtom (entry : Entry String NormalLabelKind) : Atom :=
  .expression
    [.symbol "mm-normal-label-entry", stringAtom entry.key,
      normalLabelKindAtom entry.value]

/-- Exact active normal-proof label scope.  Inactive hypotheses are absent;
assertions remain because Metamath assertions persist across block exit. -/
def normalLabelInventory (state : SourceState) :
    List (Entry String NormalLabelKind) :=
  state.activeHypotheses.map (fun hypothesis =>
      (⟨hypothesis.label, .hypothesis⟩ : Entry String NormalLabelKind)) ++
    state.assertions.map (fun assertion =>
      (⟨assertion.label, .assertion⟩ : Entry String NormalLabelKind))

/-- The semantic occurrence-indexed artifact from which concrete candidate
rows are emitted. -/
def semanticLabelArtifact (state : SourceState) :
    ReifiedArtifact (Entry String NormalLabelKind) :=
  reifiedInventory (normalLabelInventory state)

/-- Encode one typed linked occurrence as passive MM2 data. -/
def normalLabelCandidateRow (proofOwner : Atom)
    (row : Row (Entry String NormalLabelKind)) : Atom :=
  linkedRow "normal-label-candidate" proofOwner row.position row.successor
    (normalLabelEntryAtom row.value)

/-- Exact occurrence rows emitted from the generic reified artifact. -/
def normalLabelCandidateRows (proofOwner : Atom) (state : SourceState) :
    List Atom :=
  (semanticLabelArtifact state).target.map
    (normalLabelCandidateRow proofOwner)

/-- Explicit end witness for finite negative lookup. -/
def normalLabelFrontierRow (proofOwner : Atom) (state : SourceState) : Atom :=
  .expression
    [.symbol "mm-normal-label-frontier", proofOwner,
      natAtom (normalLabelInventory state).length]

/-- Complete passive inventory supplied to one theorem proof occurrence. -/
def normalLabelInventoryRows (proofOwner : Atom) (state : SourceState) :
    List Atom :=
  normalLabelCandidateRows proofOwner state ++
    [normalLabelFrontierRow proofOwner state]

/-- OSLF-derived native theory of the lookup machine actually used by this
instance. -/
def normalLabelLookupNTT :=
  lookupNTT String NormalLabelKind

/-- OSLF-derived native theory of its linked finite carrier. -/
def normalLabelCarrierNTT :=
  inventoryNTT String NormalLabelKind

/-- The typed linked representation decodes to precisely the active source
label inventory. -/
theorem semanticLabelArtifact_decodes_exact (state : SourceState) :
    decodeInventory? (semanticLabelArtifact state).target =
      some (normalLabelInventory state) := by
  exact reifiedInventory_decodes_exact (normalLabelInventory state)

/-- Every emitted candidate row comes from one exact source occurrence in
the OSLF-governed linked artifact. -/
theorem mem_normalLabelCandidateRows_iff (proofOwner row : Atom)
    (state : SourceState) :
    row ∈ normalLabelCandidateRows proofOwner state ↔
      ∃ occurrence ∈ (semanticLabelArtifact state).target,
        normalLabelCandidateRow proofOwner occurrence = row := by
  simp [normalLabelCandidateRows]

/-- Candidate membership cannot invent a label: it is backed by an active
hypothesis occurrence or an already admitted assertion occurrence. -/
theorem normalLabelInventory_member_source
    (state : SourceState) (entry : Entry String NormalLabelKind)
    (member : entry ∈ normalLabelInventory state) :
    (∃ hypothesis ∈ state.activeHypotheses,
        entry = ⟨hypothesis.label, .hypothesis⟩) ∨
      (∃ assertion ∈ state.assertions,
        entry = ⟨assertion.label, .assertion⟩) := by
  simp only [normalLabelInventory, List.mem_append, List.mem_map] at member
  rcases member with ⟨hypothesis, hypothesisMember, rfl⟩ |
      ⟨assertion, assertionMember, rfl⟩
  · exact Or.inl ⟨hypothesis, hypothesisMember, rfl⟩
  · exact Or.inr ⟨assertion, assertionMember, rfl⟩

/-- The source-derived lookup returns missing exactly when neither active
hypotheses nor admitted assertions carry the submitted label. -/
theorem normalLabelLookup_missing_iff (state : SourceState) (label : String) :
    lookup label (normalLabelInventory state) =
        .missing (normalLabelInventory state).length ↔
      (∀ hypothesis ∈ state.activeHypotheses,
        hypothesis.label ≠ label) ∧
      (∀ assertion ∈ state.assertions,
        assertion.label ≠ label) := by
  have generic :=
    lookupFrom_missing_iff (Value := NormalLabelKind) 0 label
      (normalLabelInventory state)
  simp only [Nat.zero_add] at generic
  rw [lookup, generic]
  simp only [normalLabelInventory, List.mem_append, List.mem_map]
  constructor
  · intro absent
    constructor
    · intro hypothesis member equal
      exact absent ⟨hypothesis.label, .hypothesis⟩
        (Or.inl ⟨hypothesis, member, rfl⟩) equal
    · intro assertion member equal
      exact absent ⟨assertion.label, .assertion⟩
        (Or.inr ⟨assertion, member, rfl⟩) equal
  · rintro ⟨hypothesesAbsent, assertionsAbsent⟩ entry member
    rcases member with ⟨hypothesis, hypothesisMember, rfl⟩ |
        ⟨assertion, assertionMember, rfl⟩
    · exact hypothesesAbsent hypothesis hypothesisMember
    · exact assertionsAbsent assertion assertionMember

/-- Positive source canary: an active hypothesis is found at its occurrence. -/
private def activeHypothesisCanary : SourceState :=
  { initialState with
    activeHypotheses := [.floating "hx" "wff" "x"] }

example :
    lookup "hx" (normalLabelInventory activeHypothesisCanary) =
      .found 0 .hypothesis := by
  rfl

/-- Negative source canary: an unlisted label reaches the explicit frontier. -/
example :
    lookup "missing" (normalLabelInventory activeHypothesisCanary) =
      .missing 1 := by
  rfl

#print axioms semanticLabelArtifact_decodes_exact
#print axioms mem_normalLabelCandidateRows_iff
#print axioms normalLabelInventory_member_source
#print axioms normalLabelLookup_missing_iff

end Mettapedia.Languages.Metamath.MM2NormalLabelInventory
