import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.RigidCoordinateIndexCompilation

/-!
# Certified rigid indexing for finite ground fact providers

A generated semantic provider often exposes a finite, immutable bag of ground
rows.  A query may be open, but whenever one selected coordinate has a visible
rigid root, only rows with the same root can match.  This module turns that
local property into an order-preserving index refinement.

The source observation scans every row and applies an arbitrary final matcher.
The indexed observation first performs the rigid-root filter, then invokes the
same matcher.  The only semantic obligation is the ordinary matcher-soundness
fact: an accepted row is a ground instance of the query coordinate.  The main
theorem preserves exact row order and occurrence multiplicity.  An open query
has no rigid key and deliberately falls back to the complete source bag.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteGroundFactIndexCompilation

open Mettapedia.GSLT.Parsing.HornCertificate
open RigidCoordinateIndexCompilation

mutual
  /-- Re-embed a ground term as a variable-free source term. -/
  def quoteGroundTerm : GroundTerm -> Term
    | .atom name => .atom name
    | .integer value => .integer value
    | .app constructor arguments =>
        .app constructor (quoteGroundTerms arguments)

  def quoteGroundTerms : GroundTerms -> Terms
    | .nil => .nil
    | .cons head tail =>
        .cons (quoteGroundTerm head) (quoteGroundTerms tail)
end

mutual
  /-- Quoting a ground value introduces no substitution dependency. -/
  theorem instantiate_quoteGroundTerm (term : GroundTerm)
      (substitution : Substitution) :
      instantiateTerm substitution (quoteGroundTerm term) = some term := by
    cases term with
    | atom name => rfl
    | integer value => rfl
    | app constructor arguments =>
        simp only [quoteGroundTerm, instantiateTerm, Option.bind_eq_bind]
        rw [instantiate_quoteGroundTerms arguments substitution]
        rfl

  theorem instantiate_quoteGroundTerms (terms : GroundTerms)
      (substitution : Substitution) :
      instantiateTerms substitution (quoteGroundTerms terms) = some terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp only [quoteGroundTerms, instantiateTerms, Option.bind_eq_bind]
        rw [instantiate_quoteGroundTerm head substitution,
          instantiate_quoteGroundTerms tail substitution]
        rfl
end

/-- One provider-row occurrence.  `payload` may be the complete row, a proof
record, or any other value whose order and multiplicity are observable. -/
structure GroundFact (Payload : Type) where
  coordinate : GroundTerm
  payload : Payload
deriving DecidableEq, Repr

/-- A ground fact always supplies a rigid root key. -/
def factKey (fact : GroundFact Payload) : DispatchKey :=
  match fact.coordinate with
  | .atom name => .atom name
  | .integer value => .integer value
  | .app constructor arguments =>
      .application constructor (termsLength (quoteGroundTerms arguments))

@[simp] theorem rootKey_quoteGroundTerm (term : GroundTerm) :
    rootKey? (quoteGroundTerm term) =
      some (factKey ({ coordinate := term, payload := () } : GroundFact Unit)) := by
  cases term with
  | atom name => rfl
  | integer value => rfl
  | app constructor arguments => rfl

/-- Root-compatible candidate selection.  An open query retains every row. -/
def selected (query : Term) (fact : GroundFact Payload) : Bool :=
  match rootKey? query with
  | none => true
  | some key => factKey fact == key

def candidates (query : Term) (facts : List (GroundFact Payload)) :
    List (GroundFact Payload) :=
  facts.filter (selected query)

/-- A row that is an accepted ground instance cannot be removed by the rigid
index. -/
theorem mem_candidates_of_instance
    (query : Term) (facts : List (GroundFact Payload))
    (fact : GroundFact Payload) (member : fact ∈ facts)
    (substitution : Substitution)
    (instantiated :
      instantiateTerm substitution query = some fact.coordinate) :
    fact ∈ candidates query facts := by
  cases queryKeyEq : rootKey? query with
  | none =>
      apply List.mem_filter.mpr
      exact ⟨member, by simp [selected, queryKeyEq]⟩
  | some queryKey =>
      have compatible := rootCompatible_of_commonGroundInstance
        query (quoteGroundTerm fact.coordinate) substitution []
        fact.coordinate instantiated
        (instantiate_quoteGroundTerm fact.coordinate [])
      have factKeyEq :
          rootKey? (quoteGroundTerm fact.coordinate) =
            some (factKey fact) := by
        cases fact with
        | mk coordinate payload => cases coordinate <;> rfl
      simp [rootCompatible, queryKeyEq, factKeyEq] at compatible
      apply List.mem_filter.mpr
      exact ⟨member, by simp [selected, queryKeyEq, compatible]⟩

/-- Source provider semantics: run the final matcher on every occurrence. -/
def sourceMatches (accepts : GroundFact Payload -> Bool)
    : List (GroundFact Payload) -> List Payload
  | [] => []
  | fact :: facts =>
      if accepts fact then
        fact.payload :: sourceMatches accepts facts
      else
        sourceMatches accepts facts

/-- Indexed provider semantics: inspect only root-compatible occurrences. -/
def indexedMatches (query : Term)
    (accepts : GroundFact Payload -> Bool)
    : List (GroundFact Payload) -> List Payload
  | [] => []
  | fact :: facts =>
      if selected query fact && accepts fact then
        fact.payload :: indexedMatches query accepts facts
      else
        indexedMatches query accepts facts

/-- Exact provider refinement.  A matcher-soundness certificate is enough to
show that every row rejected by the index would also fail the final matcher. -/
theorem indexedMatches_eq_sourceMatches
    (query : Term) (accepts : GroundFact Payload -> Bool)
    (facts : List (GroundFact Payload))
    (matchSound : ∀ fact ∈ facts, accepts fact = true ->
      ∃ substitution,
        instantiateTerm substitution query = some fact.coordinate) :
    indexedMatches query accepts facts = sourceMatches accepts facts := by
  induction facts with
  | nil => rfl
  | cons fact facts inductionHypothesis =>
      have tailSound : ∀ candidate ∈ facts, accepts candidate = true ->
          ∃ substitution,
            instantiateTerm substitution query = some candidate.coordinate := by
        intro candidate member accepted
        exact matchSound candidate (by simp [member]) accepted
      have tailEq := inductionHypothesis tailSound
      by_cases accepted : accepts fact = true
      · obtain ⟨substitution, instantiated⟩ :=
          matchSound fact (by simp) accepted
        have selectedTrue : selected query fact = true :=
          (List.mem_filter.mp
            (mem_candidates_of_instance query (fact :: facts) fact
              (by simp) substitution instantiated)).2
        simp [indexedMatches, sourceMatches, accepted,
          selectedTrue, tailEq]
      · have acceptedFalse : accepts fact = false :=
          Bool.eq_false_of_not_eq_true accepted
        simp [indexedMatches, sourceMatches, acceptedFalse,
          tailEq]

/-- The index never inspects more physical rows than the source scan. -/
theorem candidates_length_le (query : Term)
    (facts : List (GroundFact Payload)) :
    (candidates query facts).length <= facts.length := by
  exact List.length_filter_le _ _

/-- A coordinate is locally useful exactly when its finite ground bag exposes
at least two different rigid roots. -/
def useful (facts : List (GroundFact Payload)) : Bool :=
  facts.any fun left =>
    facts.any fun right => factKey left != factKey right

/-- Admitted provider query carrying the independent matcher-soundness
certificate used by the realization. -/
structure AdmittedProviderQuery (Payload : Type) where
  query : Term
  facts : List (GroundFact Payload)
  accepts : GroundFact Payload -> Bool
  matchSound : ∀ fact ∈ facts, accepts fact = true ->
    ∃ substitution,
      instantiateTerm substitution query = some fact.coordinate

/-- Query-specialized artifact emitted by the finite-fact index compiler.
Unlike the source object it contains only the rows admitted by the rigid-key
index. -/
structure IndexedProviderQuery (Payload : Type) where
  facts : List (GroundFact Payload)
  accepts : GroundFact Payload -> Bool

/-- Compile an admitted provider query to its ordered candidate bag. -/
def compileProvider (source : AdmittedProviderQuery Payload) :
    IndexedProviderQuery Payload where
  facts := candidates source.query source.facts
  accepts := source.accepts

/-- Compilation cannot increase the number of physical matcher calls. -/
theorem compileProvider_facts_length_le
    (source : AdmittedProviderQuery Payload) :
    (compileProvider source).facts.length <= source.facts.length := by
  exact candidates_length_le source.query source.facts

/-- Filtering the physical bag first is exactly the recursive indexed
observation.  In particular, `List.filter` retains source order and duplicate
occurrences. -/
theorem sourceMatches_candidates_eq_indexedMatches
    (query : Term) (accepts : GroundFact Payload -> Bool)
    (facts : List (GroundFact Payload)) :
    sourceMatches accepts (candidates query facts) =
      indexedMatches query accepts facts := by
  induction facts with
  | nil => rfl
  | cons fact facts inductionHypothesis =>
      have tailEq :
          sourceMatches accepts (List.filter (selected query) facts) =
            indexedMatches query accepts facts := by
        simpa only [candidates] using inductionHypothesis
      by_cases selectedFact : selected query fact = true
      · by_cases acceptedFact : accepts fact = true
        · simp [candidates, sourceMatches, indexedMatches, selectedFact,
            acceptedFact, tailEq]
        · have acceptedFalse : accepts fact = false :=
            Bool.eq_false_of_not_eq_true acceptedFact
          simp [candidates, sourceMatches, indexedMatches, selectedFact,
            acceptedFalse, tailEq]
      · have selectedFalse : selected query fact = false :=
          Bool.eq_false_of_not_eq_true selectedFact
        simp [candidates, indexedMatches, selectedFalse, tailEq]

/-- Generated rigid-fact indexing as a composable certified realization. -/
def finiteGroundFactIndexRealization :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedProviderQuery Payload)
      (IndexedProviderQuery Payload)
      (List Payload) where
  compile := fun _ source => compileProvider source
  observeSource := fun _ source =>
    sourceMatches source.accepts source.facts
  observeArtifact := fun _ artifact =>
    sourceMatches artifact.accepts artifact.facts
  adequate := by
    intro _ source
    change sourceMatches source.accepts
        (candidates source.query source.facts) =
      sourceMatches source.accepts source.facts
    rw [sourceMatches_candidates_eq_indexedMatches]
    exact indexedMatches_eq_sourceMatches source.query source.accepts
      source.facts source.matchSound

/-! ## Independent provider canaries -/

private def proofRows : List (GroundFact String) :=
  [{ coordinate := .app "normal" (.ofList [.atom "a"]), payload := "n0" },
   { coordinate := .app "compressed" (.ofList [.atom "b"]), payload := "c0" },
   { coordinate := .app "normal" (.ofList [.atom "c"]), payload := "n1" }]

private def clauseRows : List (GroundFact String) :=
  [{ coordinate := .app "positive" (.ofList [.atom "p"]), payload := "p" },
   { coordinate := .app "negative" (.ofList [.atom "q"]), payload := "n" }]

/-- A proof-like finite table retains both matching occurrences in source
order. -/
example :
    (candidates (.app "normal" (.ofList [.var 0])) proofRows).map
      GroundFact.payload = ["n0", "n1"] := by
  decide

/-- A clause-polarity table independently exercises the same transform. -/
example :
    useful clauseRows = true ∧
      (candidates (.app "negative" (.ofList [.var 0])) clauseRows).map
        GroundFact.payload = ["n"] := by
  decide

/-- An open coordinate has no rigid key and retains every occurrence. -/
example : candidates (.var 0) proofRows = proofRows := by
  decide

/-- A single-key table is correctly rejected as unprofitable. -/
example :
    useful [{ coordinate := .atom "same", payload := "left" },
      { coordinate := .atom "same", payload := "right" }] = false := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteGroundFactIndexCompilation
