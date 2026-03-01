import Mettapedia.OSLF.PeTTa.Answers
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# PeTTa Atomspace Semantics

An atomspace is PeTTa's mutable store of patterns (facts) and rewrite rules.
This file formalizes the **pure** (effect-free) interface to atomspaces:
- Structure: facts + rules
- Queries: `spaceMatch s pat tmpl` — find all groundings of `tmpl` via
  pattern matching `pat` against facts in `s`
- Mutators: `addAtom`, `removeAtom` (pure, returning a new space)

## Alignment with PeTTa / MeTTa Spec

MeTTa spec: `(match &self pat tmpl)` iterates over the atomspace, pattern-matches
`pat` against each atom, and returns a `superpose` of `tmpl` instantiated by
each successful matching.

PeTTa transpiler: `match_term/3` in `spaces.pl` implements this via Prolog
backtracking. The formal `spaceMatch` corresponds to collecting all solutions.

## References

- MeTTa spec §match: `trueagi-io.github.io/hyperon-experimental/metta/`
- PeTTa spaces.pl: `hyperon/PeTTa/spaces.pl`
-/

namespace Mettapedia.OSLF.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Atomspace Structure -/

/-- A PeTTa atomspace: a finite collection of ground (or ground-ish) patterns (facts),
    together with a list of rewrite rules defining the language semantics.

    In the pure fragment, facts are immutable. Mutation is modeled by returning
    a new space (see `addAtom`, `removeAtom`). -/
structure PeTTaSpace where
  /-- The EDB: ground atoms stored in the space (modeled as a list). -/
  facts : List Pattern
  /-- The IDB: rewrite rules `(= lhs rhs)` for pure evaluation. -/
  rules : List RewriteRule

namespace PeTTaSpace

/-! ## Space Operations -/

/-- The empty atomspace. -/
def empty : PeTTaSpace := { facts := [], rules := [] }

/-- Add an atom to the space (returns a new space). -/
def addAtom (s : PeTTaSpace) (p : Pattern) : PeTTaSpace :=
  { s with facts := p :: s.facts }

/-- Remove all occurrences of an atom from the space. -/
def removeAtom (s : PeTTaSpace) (p : Pattern) : PeTTaSpace :=
  { s with facts := s.facts.filter (· != p) }

/-- Add a rewrite rule to the space. -/
def addRule (s : PeTTaSpace) (r : RewriteRule) : PeTTaSpace :=
  { s with rules := r :: s.rules }

/-! ## Space Pattern Matching -/

/-- Match `pat` against all facts in the space; for each successful match,
    apply the resulting bindings to `tmpl` and collect the results.

    This models MeTTa's `(match &self pat tmpl)`:
    - Iterate over all facts in the atomspace
    - For each fact `f`, run `matchPattern pat f` (may return multiple bindings)
    - For each binding set `bs`, compute `applyBindings bs tmpl`
    - Collect all such results as a list (nondeterministic answers) -/
def spaceMatch (s : PeTTaSpace) (pat tmpl : Pattern) : Answers :=
  s.facts.flatMap fun fact =>
    (matchPattern pat fact).map fun bs => applyBindings bs tmpl

/-! ## Soundness of spaceMatch -/

/-- **Soundness of `spaceMatch`**: every answer `q ∈ spaceMatch s pat tmpl`
    arises from matching `pat` against some fact in the space and applying
    the resulting bindings to `tmpl`.

    Concretely: there exists a fact `fact ∈ s.facts` and bindings
    `bs ∈ matchPattern pat fact` such that `q = applyBindings bs tmpl`. -/
theorem spaceMatch_sound (s : PeTTaSpace) (pat tmpl : Pattern) (q : Pattern)
    (h : q ∈ spaceMatch s pat tmpl) :
    ∃ fact ∈ s.facts, ∃ bs ∈ matchPattern pat fact, q = applyBindings bs tmpl := by
  unfold spaceMatch at h
  rw [List.mem_flatMap] at h
  obtain ⟨fact, hfact, hmem⟩ := h
  rw [List.mem_map] at hmem
  obtain ⟨bs, hbs, heq⟩ := hmem
  exact ⟨fact, hfact, bs, hbs, heq.symm⟩

/-- **Completeness of `spaceMatch`**: every pairing (fact, bindings) that
    successfully matches produces an answer. -/
theorem spaceMatch_complete (s : PeTTaSpace) (pat tmpl : Pattern)
    (fact : Pattern) (bs : Bindings)
    (hfact : fact ∈ s.facts) (hbs : bs ∈ matchPattern pat fact) :
    applyBindings bs tmpl ∈ spaceMatch s pat tmpl := by
  unfold spaceMatch
  rw [List.mem_flatMap]
  exact ⟨fact, hfact, List.mem_map.mpr ⟨bs, hbs, rfl⟩⟩

/-- `spaceMatch` on an empty space yields no answers. -/
@[simp]
theorem spaceMatch_empty (pat tmpl : Pattern) :
    spaceMatch PeTTaSpace.empty pat tmpl = [] := by
  simp [spaceMatch, PeTTaSpace.empty]

/-- Membership characterization for `spaceMatch`. -/
theorem mem_spaceMatch {s : PeTTaSpace} {pat tmpl q : Pattern} :
    q ∈ spaceMatch s pat tmpl ↔
    ∃ fact ∈ s.facts, ∃ bs ∈ matchPattern pat fact, q = applyBindings bs tmpl :=
  ⟨spaceMatch_sound s pat tmpl q, fun ⟨fact, hf, bs, hbs, heq⟩ =>
    heq ▸ spaceMatch_complete s pat tmpl fact bs hf hbs⟩

/-! ## Properties of addAtom / removeAtom -/

/-- Facts in the original space are preserved after `addAtom`. -/
theorem mem_facts_addAtom {s : PeTTaSpace} {p fact : Pattern} (h : fact ∈ s.facts) :
    fact ∈ (s.addAtom p).facts :=
  List.mem_cons_of_mem _ h

/-- The added atom is a fact in the new space. -/
theorem mem_facts_addAtom_self (s : PeTTaSpace) (p : Pattern) :
    p ∈ (s.addAtom p).facts :=
  List.mem_cons_self

/-- Facts in `removeAtom` are a subset of the original facts. -/
theorem mem_facts_removeAtom_subset {s : PeTTaSpace} {p fact : Pattern}
    (h : fact ∈ (s.removeAtom p).facts) : fact ∈ s.facts := by
  simp [removeAtom] at h
  exact h.1

end PeTTaSpace

/-! ## Summary

**0 sorries. 0 axioms.**

### Structure
- `PeTTaSpace` — atomspace with `facts : List Pattern` and `rules : List RewriteRule`
- `PeTTaSpace.empty`, `addAtom`, `removeAtom`, `addRule`

### Queries
- `spaceMatch s pat tmpl : Answers` — models MeTTa's `(match &self pat tmpl)`
- `spaceMatch_sound` — every answer comes from a matching fact
- `spaceMatch_complete` — every match produces an answer
- `mem_spaceMatch` — full characterization

### Mutation (pure, returns new space)
- `mem_facts_addAtom`, `mem_facts_addAtom_self` — addAtom preserves/adds facts
- `mem_facts_removeAtom_subset` — removeAtom only removes facts
-/

end Mettapedia.OSLF.PeTTa
