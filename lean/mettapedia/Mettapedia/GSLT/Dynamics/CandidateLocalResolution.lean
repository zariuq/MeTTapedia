import Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility

/-!
# Candidate-local evaluation and bag-relative resolution

A pure valued clause has two candidate-local stages: compute a value and use
that value to emit zero or one result.  Extensionally, this is an ordinary
partial map on one candidate.  Its hidden value channel can improve syntax,
sharing, and compilation without adding a new local behavior.

Applying a candidate-local clause to a bag is additive: disjoint input bags
may be processed independently and their outputs combined.  This law is the
precise source of streaming, parallel-map, and early-filtering opportunities.

Some operations are necessarily bag-relative.  This module complements the
existing exact maximum-selection and normalized-share theorems by isolating
their algebraic obstruction: every candidate-local bag program preserves bag
addition, whereas maximum selection does not.  Normalization, top-k, sampling
from a total rate, and measurement have the same whole-race shape, although
their additional algebras and effects differ.

Thus local grading and global resolution are complementary interfaces.  A
value carrier by itself chooses neither one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CandidateLocalResolution

open Mettapedia.GSLT.Core

universe uCandidate uValue uOutput

/-! ## Pure candidate-local clauses -/

/-- Compute a value for one candidate, then use it to emit zero or one
result.  The value need not be stored in the source atom. -/
structure Clause (Candidate : Type uCandidate) (Value : Type uValue)
    (Output : Type uOutput) where
  value : Candidate → Value
  emit : Candidate → Value → Option Output

namespace Clause

/-- Erase the internal value wire to the ordinary partial map it denotes. -/
def lower {Candidate : Type uCandidate} {Value : Type uValue}
    {Output : Type uOutput} (clause : Clause Candidate Value Output) :
    Candidate → Option Output :=
  fun candidate => clause.emit candidate (clause.value candidate)

/-- Any ordinary candidate-local partial map has a unit-valued clause view.
This is the converse extensional encoding for pure local behavior. -/
def ofPartial {Candidate : Type uCandidate} {Output : Type uOutput}
    (program : Candidate → Option Output) :
    Clause Candidate Unit Output where
  value := fun _ => ()
  emit := fun candidate _ => program candidate

@[simp] theorem lower_ofPartial
    {Candidate : Type uCandidate} {Output : Type uOutput}
    (program : Candidate → Option Output) :
    (ofPartial program).lower = program := by
  funext candidate
  rfl

/-- Pure local grading therefore factors through an ordinary local partial
map.  This theorem is extensional: it does not erase the usefulness of a
named value wire for compilation or provenance. -/
theorem pure_local_extensional_equivalence
    {Candidate : Type uCandidate} {Value : Type uValue}
    {Output : Type uOutput} (clause : Clause Candidate Value Output) :
    (ofPartial clause.lower).lower = clause.lower := by
  exact lower_ofPartial clause.lower

/-- Apply one local clause independently to every occurrence of a bag. -/
def runBag {Candidate : Type uCandidate} {Value : Type uValue}
    {Output : Type uOutput} (clause : Clause Candidate Value Output)
    (candidates : Multiset Candidate) : Multiset Output :=
  candidates.filterMap clause.lower

/-- Candidate-local execution is additive over bags. -/
theorem runBag_add
    {Candidate : Type uCandidate} {Value : Type uValue}
    {Output : Type uOutput} (clause : Clause Candidate Value Output)
    (left right : Multiset Candidate) :
    clause.runBag (left + right) = clause.runBag left + clause.runBag right := by
  exact Multiset.filterMap_add clause.lower left right

end Clause

/-! ## The exact locality criterion -/

/-- A bag transformation is candidate-local when one fixed partial map is
applied independently to every occurrence. -/
def CandidateLocalizable
    {Candidate : Type uCandidate} {Output : Type uOutput}
    (transform : Multiset Candidate → Multiset Output) : Prop :=
  ∃ localStep : Candidate → Option Output,
    ∀ candidates, transform candidates = candidates.filterMap localStep

/-- Every candidate-localizable transformation is additive. -/
theorem additive_of_candidateLocalizable
    {Candidate : Type uCandidate} {Output : Type uOutput}
    {transform : Multiset Candidate → Multiset Output}
    (localizable : CandidateLocalizable transform) :
    ∀ left right,
      transform (left + right) = transform left + transform right := by
  obtain ⟨localStep, equality⟩ := localizable
  intro left right
  rw [equality, Multiset.filterMap_add, ← equality, ← equality]

/-- Every pure valued clause supplies a candidate-localizable bag
transformation. -/
theorem clause_runBag_candidateLocalizable
    {Candidate : Type uCandidate} {Value : Type uValue}
    {Output : Type uOutput} (clause : Clause Candidate Value Output) :
    CandidateLocalizable clause.runBag := by
  exact ⟨clause.lower, fun _ => rfl⟩

/-! ## Positive local filtering -/

/-- A crisp local guard is a Boolean-valued instance of the interface. -/
def guardedClause {Candidate : Type uCandidate} (guard : Candidate → Bool) :
    Clause Candidate Bool Candidate where
  value := guard
  emit := fun candidate accepted => if accepted then some candidate else none

/-- A rejected occurrence is removed without inspecting any competitor. -/
@[simp] theorem guardedClause_rejects
    {Candidate : Type uCandidate} (guard : Candidate → Bool)
    (candidate : Candidate) (rejected : guard candidate = false) :
    (guardedClause guard).lower candidate = none := by
  simp [Clause.lower, guardedClause, rejected]

/-- An accepted occurrence is emitted without inspecting any competitor. -/
@[simp] theorem guardedClause_accepts
    {Candidate : Type uCandidate} (guard : Candidate → Bool)
    (candidate : Candidate) (accepted : guard candidate = true) :
    (guardedClause guard).lower candidate = some candidate := by
  simp [Clause.lower, guardedClause, accepted]

/-! ## Bag-relative maximum is not additive -/

/-- Exact maximum selection fails bag addition as soon as one candidate
strictly outweighs another.  Separately resolving the singleton races keeps
both candidates; resolving their combined race removes the lower one. -/
theorem maxSelector_not_additive
    {Candidate : Type uCandidate} (weight : Candidate → Nat)
    {low high : Candidate} (outweighed : weight low < weight high) :
    ¬ ∀ left right : Multiset Candidate,
      maxSelector weight (left + right) =
        maxSelector weight left + maxSelector weight right := by
  classical
  intro additive
  have lowAlone : low ∈ maxSelector weight ({low} : Multiset Candidate) := by
    rw [maxSelector_isMaxSelection]
    simp
  have lowInSeparate :
      low ∈ maxSelector weight ({low} : Multiset Candidate) +
        maxSelector weight ({high} : Multiset Candidate) := by
    exact Multiset.mem_add.mpr (Or.inl lowAlone)
  have combinedEquality :=
    additive ({low} : Multiset Candidate) ({high} : Multiset Candidate)
  have lowInCombined :
      low ∈ maxSelector weight ({low, high} : Multiset Candidate) := by
    change low ∈ maxSelector weight
      (({low} : Multiset Candidate) + ({high} : Multiset Candidate))
    rw [combinedEquality]
    exact lowInSeparate
  have maximal := (maxSelector_isMaxSelection weight
    ({low, high} : Multiset Candidate) low).mp lowInCombined
  have highLeLow : weight high ≤ weight low := maximal.2 high (by simp)
  exact (not_le.mpr outweighed) highLeLow

/-- Consequently exact maximum selection cannot be implemented by any pure
candidate-local partial map.  This reuses the canonical selector and
specification from `GradedSelectionIrreducibility`; the new content is the
commutative-monoid obstruction needed by streaming and parallel-map
compilers. -/
theorem maxSelector_not_candidateLocalizable
    {Candidate : Type uCandidate} (weight : Candidate → Nat)
    {low high : Candidate} (outweighed : weight low < weight high) :
    ¬ CandidateLocalizable (maxSelector weight) := by
  intro localizable
  exact maxSelector_not_additive weight outweighed
    (additive_of_candidateLocalizable localizable)

/-! ## Axiom audit targets -/

#print axioms Clause.runBag_add
#print axioms Clause.pure_local_extensional_equivalence
#print axioms additive_of_candidateLocalizable
#print axioms maxSelector_not_candidateLocalizable

end Mettapedia.GSLT.Dynamics.CandidateLocalResolution
