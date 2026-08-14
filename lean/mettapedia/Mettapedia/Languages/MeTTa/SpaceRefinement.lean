/-
# Proof-relevant space refinements

The candidate type form `Space P` classifies a space whose every stored atom
matches `P`.  This file gives its semantics but does not claim that a current
syntax parser already accepts that spelling.  It is a parametrized typing
judgment, not ordinary membership:

  `space : Space P`  means  `forall atom in space, exists binding, match P atom binding`.

The existential binding is local to each atom.  A successful check may expose
the flat bag of bindings for query use, but the proof-relevant witness is a
dependent function selecting a binding for every occurrence in the space.

The final section places this judgment under a context.  Pointwise space
typing is exactly universal image along the context projection, so the word
`forall` is justified by the actual predicate-fibre right adjoint rather than
by an analogy with `match`.
-/

import Mathlib.Data.Multiset.Fintype
import Mettapedia.Languages.MeTTa.MatchAllContract

namespace Mettapedia.Languages.MeTTa.SpaceRefinement

open Mettapedia.Languages.MeTTa.MatchAllContract
open Mettapedia.Languages.MeTTa.MatchAllContract.PredicateQuantifier

universe uContext uAtom uPattern uBinding

/-- The semantic type former proposed for the syntax form `Space P`. -/
structure SpaceType (Pattern : Type uPattern) where
  pattern : Pattern
deriving DecidableEq, Repr

/-- A matcher is indexed by the pattern being used as a space refinement. -/
abbrev Matcher (Pattern : Type uPattern) (Atom : Type uAtom)
    (Binding : Type uBinding) :=
  Pattern → Atom → Multiset Binding

/-- The proposition asserted by `space : Space P`. -/
def SpaceHasType (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern) : Prop :=
  ∀ atom ∈ space, ∃ binding, binding ∈ matchOne type.pattern atom

/-- One occurrence of an atom in a multiset space.  Mathlib represents it as
an atom paired with a finite index below that atom's multiplicity. -/
abbrev Occurrence [DecidableEq Atom] (space : Multiset Atom) :=
  Multiset.ToType space

/-- Proof-relevant evidence for a space refinement: each atom occurrence has
its own matching binding.  There is generally no single environment shared by
all atoms. -/
def TypingEvidence [DecidableEq Atom]
    (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern) : Type _ :=
  (occurrence : Occurrence space) →
    { binding : Binding // binding ∈ matchOne type.pattern occurrence.1 }

/-- Proof-relevant evidence entails the ordinary refinement proposition. -/
theorem evidence_sound
    [DecidableEq Atom]
    (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern)
    (evidence : TypingEvidence matchOne space type) :
    SpaceHasType matchOne space type := by
  intro atom member
  let occurrence : Occurrence space :=
    Multiset.mkToType space atom ⟨0, Multiset.count_pos.mpr member⟩
  let witness := evidence occurrence
  exact ⟨witness.1, witness.2⟩

/-- Conversely, a proof of the refinement supplies a dependent witness.
The choice is proof-level; the executable checker below returns all computed
bindings rather than relying on this construction. -/
noncomputable def evidenceOfHasType
    [DecidableEq Atom]
    (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern)
    (typed : SpaceHasType matchOne space type) :
    TypingEvidence matchOne space type :=
  fun occurrence =>
    let existsBinding := typed occurrence.1 Multiset.coe_mem
    ⟨Classical.choose existsBinding, Classical.choose_spec existsBinding⟩

/-- Executable checking is the existing proof-relevant inclusion scan. -/
def check (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern) :
    InclusionOutcome Atom Binding :=
  checkInclusion (matchOne type.pattern) space

/-- The executable ascription accepts exactly the semantic typing judgment. -/
theorem check_holds_iff
    (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern) :
    check matchOne space type =
        .holds (successfulBindings (matchOne type.pattern) space) ↔
      SpaceHasType matchOne space type := by
  simpa [check, SpaceHasType] using
    checkInclusion_holds_iff_forall_exists_binding
      (matchOne type.pattern) space

/-- Executable acceptance is equivalent to inhabitation of the dependent
per-occurrence witness type.  This is the direct bridge between the finite
checker and proof-relevant space typing. -/
theorem check_holds_iff_nonempty_evidence
    [DecidableEq Atom]
    (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern) :
    check matchOne space type =
        .holds (successfulBindings (matchOne type.pattern) space) ↔
      Nonempty (TypingEvidence matchOne space type) := by
  constructor
  · intro accepted
    exact ⟨evidenceOfHasType matchOne space type
      ((check_holds_iff matchOne space type).mp accepted)⟩
  · rintro ⟨evidence⟩
    exact (check_holds_iff matchOne space type).mpr
      (evidence_sound matchOne space type evidence)

/-- Failed checking returns precisely the atoms which prevent the ascription. -/
theorem check_violations_iff
    (matchOne : Matcher Pattern Atom Binding)
    (space : Multiset Atom) (type : SpaceType Pattern)
    (violations : Multiset Atom) :
    check matchOne space type = .violations violations ↔
      violations = violationBag (matchOne type.pattern) space ∧
        violations ≠ 0 := by
  exact checkInclusion_violations_iff
    (matchOne type.pattern) space violations

/-! ## Context-parametrized space typing -/

/-- A family of space refinements varying over an ordinary typing context. -/
structure ContextualAscription
    (Context : Type uContext) (Atom : Type uAtom)
    (Pattern : Type uPattern) where
  space : Context → Multiset Atom
  type : Context → SpaceType Pattern

/-- Contextual space typing is evaluated pointwise in the current context. -/
def ContextualAscription.HasType
    (ascription : ContextualAscription Context Atom Pattern)
    (matchOne : Context → Matcher Pattern Atom Binding)
    (context : Context) : Prop :=
  SpaceHasType (matchOne context) (ascription.space context)
    (ascription.type context)

/-- The predicate on a context extended by one candidate atom. -/
def ContextualAscription.coveragePredicate
    (ascription : ContextualAscription Context Atom Pattern)
    (matchOne : Context → Matcher Pattern Atom Binding) :
    Context × Atom → Prop :=
  fun pair =>
    pair.2 ∈ ascription.space pair.1 →
      ∃ binding,
        binding ∈ matchOne pair.1 (ascription.type pair.1).pattern pair.2

/-- The parametrized typing judgment is exactly the genuine right adjoint
`forall` along context extension/projection. -/
theorem contextual_hasType_iff_forallAlong
    (ascription : ContextualAscription Context Atom Pattern)
    (matchOne : Context → Matcher Pattern Atom Binding)
    (context : Context) :
    ascription.HasType matchOne context ↔
      forallAlong projection
        (ascription.coveragePredicate matchOne) context := by
  rw [forallAlong_projection]
  simp [ContextualAscription.HasType,
    ContextualAscription.coveragePredicate, SpaceHasType]

/-- Pull a contextual ascription back along a context substitution. -/
def ContextualAscription.reindex
    (substitution : NewContext → Context)
    (ascription : ContextualAscription Context Atom Pattern) :
    ContextualAscription NewContext Atom Pattern where
  space context := ascription.space (substitution context)
  type context := ascription.type (substitution context)

/-- Matchers reindex by ordinary precomposition. -/
def reindexMatcher
    (substitution : NewContext → Context)
    (matchOne : Context → Matcher Pattern Atom Binding) :
    NewContext → Matcher Pattern Atom Binding :=
  fun context => matchOne (substitution context)

/-- Space typing is stable under substitution of its context. -/
theorem hasType_reindex
    (substitution : NewContext → Context)
    (ascription : ContextualAscription Context Atom Pattern)
    (matchOne : Context → Matcher Pattern Atom Binding)
    (context : NewContext) :
    (ascription.reindex substitution).HasType
        (reindexMatcher substitution matchOne) context ↔
      ascription.HasType matchOne (substitution context) := by
  rfl

@[simp] theorem reindex_id
    (ascription : ContextualAscription Context Atom Pattern) :
    ascription.reindex id = ascription := by
  cases ascription
  rfl

@[simp] theorem reindex_comp
    (first : MiddleContext → Context)
    (second : NewContext → MiddleContext)
    (ascription : ContextualAscription Context Atom Pattern) :
    (ascription.reindex first).reindex second =
      ascription.reindex (first ∘ second) := by
  cases ascription
  rfl

/-! ## Executable positive and negative controls -/

/-- Equality-pattern matching, retaining a unit binding for each success. -/
def equalityMatcher (pattern atom : Nat) : Multiset Unit :=
  if pattern = atom then {()} else 0

def uniformOnes : Multiset Nat := {1, 1}
def mixedNumbers : Multiset Nat := {1, 2}
def onlyOne : SpaceType Nat := ⟨1⟩

def firstOneOccurrence : Occurrence uniformOnes :=
  Multiset.mkToType uniformOnes 1 ⟨0, by decide⟩

def secondOneOccurrence : Occurrence uniformOnes :=
  Multiset.mkToType uniformOnes 1 ⟨1, by decide⟩

/-- Duplicate equal atoms remain distinct occurrences. -/
theorem duplicate_occurrences_are_distinct :
    firstOneOccurrence ≠ secondOneOccurrence := by
  intro equal
  have equalIndices := congrArg (fun occurrence => occurrence.2.val) equal
  simp [firstOneOccurrence, secondOneOccurrence] at equalIndices

/-- Positive control: every occurrence is covered and both bindings survive. -/
example :
    check equalityMatcher uniformOnes onlyOne = .holds {(), ()} := by
  decide

/-- Negative control: the ill-shaped atom is returned, not silently dropped. -/
example :
    check equalityMatcher mixedNumbers onlyOne = .violations {2} := by
  decide

/-- A matching member does not make the whole space well typed. -/
theorem existential_match_is_not_space_typing :
    (∃ atom ∈ mixedNumbers,
        equalityMatcher onlyOne.pattern atom ≠ 0) ∧
      ¬ SpaceHasType equalityMatcher mixedNumbers onlyOne := by
  constructor
  · exact ⟨1, by simp [mixedNumbers], by simp [equalityMatcher, onlyOne]⟩
  · intro typed
    obtain ⟨binding, member⟩ := typed 2 (by simp [mixedNumbers])
    simp [equalityMatcher, onlyOne] at member

end Mettapedia.Languages.MeTTa.SpaceRefinement
