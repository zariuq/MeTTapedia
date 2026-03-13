import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# PeTTa Atomspace Semantics

An atomspace is PeTTa's mutable store of patterns (facts) and rewrite rules.
This file formalizes the **pure** (effect-free) interface to atomspaces:
- Structure: facts + rules
- Queries: `spaceMatch s pat tmpl` — find all groundings of `tmpl` via
  pattern matching `pat` against the current stored atoms of `s`
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

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Atomspace Structure -/

/-- A PeTTa atomspace: a finite collection of ground (or ground-ish) patterns (facts),
    together with a list of rewrite rules defining the language semantics.

    In the pure fragment, mutation is modeled by returning a new space
    (see `addAtom`, `removeAtom`). -/
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

 /-- Stored surface atom corresponding to a premise-free rewrite rule.

This is the narrow current slice needed for PeTTa's space library behavior:
premise-free rules are visible to `get-atoms` / variable-pattern `match` as
stored `(= lhs rhs)` atoms, mirroring upstream `spaces.pl`. Premise-bearing
rules are left out of this stored-atom view for now. -/
def storedRuleAtom? (r : RewriteRule) : Option Pattern :=
  if r.premises.isEmpty then
    some (.apply "=" [r.left, r.right])
  else
    none

/-- Remove all occurrences of an atom from the space. -/
def removeAtom (s : PeTTaSpace) (p : Pattern) : PeTTaSpace :=
  { facts := s.facts.filter (· != p)
    rules := s.rules.filter (fun r => storedRuleAtom? r != some p) }

/-- Add a rewrite rule to the space. -/
def addRule (s : PeTTaSpace) (r : RewriteRule) : PeTTaSpace :=
  { s with rules := r :: s.rules }

/-- Stored rule atoms currently visible in the atomspace query layer. -/
def storedRuleAtoms (s : PeTTaSpace) : List Pattern :=
  s.rules.filterMap storedRuleAtom?

/-- The current stored atoms visible to `match` / `get-atoms` on the default
backend atomspace: ordinary facts plus premise-free stored rewrite atoms. -/
def storedAtoms (s : PeTTaSpace) : List Pattern :=
  s.facts ++ s.storedRuleAtoms

/-! ## Space Pattern Matching -/

/-- Match `pat` against all facts in the space; for each successful match,
    apply the resulting bindings to `tmpl` and collect the results.

    This models MeTTa's `(match &self pat tmpl)`:
    - Iterate over all stored atoms in the atomspace
    - For each atom `a`, run `matchPattern pat a` (may return multiple bindings)
    - For each binding set `bs`, compute `applyBindings bs tmpl`
    - Collect all such results as a list (nondeterministic answers) -/
def spaceMatch (s : PeTTaSpace) (pat tmpl : Pattern) : Answers :=
  s.storedAtoms.flatMap fun atom =>
    (matchPattern pat atom).map fun bs => applyBindings bs tmpl

/-! ## Soundness of spaceMatch -/

/-- **Soundness of `spaceMatch`**: every answer `q ∈ spaceMatch s pat tmpl`
    arises from matching `pat` against some stored atom in the space and applying
    the resulting bindings to `tmpl`.

    Concretely: there exists an atom `atom ∈ s.storedAtoms` and bindings
    `bs ∈ matchPattern pat atom` such that `q = applyBindings bs tmpl`. -/
theorem spaceMatch_sound (s : PeTTaSpace) (pat tmpl : Pattern) (q : Pattern)
    (h : q ∈ spaceMatch s pat tmpl) :
    ∃ atom ∈ s.storedAtoms, ∃ bs ∈ matchPattern pat atom, q = applyBindings bs tmpl := by
  unfold spaceMatch at h
  rw [List.mem_flatMap] at h
  obtain ⟨atom, hatom, hmem⟩ := h
  rw [List.mem_map] at hmem
  obtain ⟨bs, hbs, heq⟩ := hmem
  exact ⟨atom, hatom, bs, hbs, heq.symm⟩

/-- **Completeness of `spaceMatch`**: every pairing (fact, bindings) that
    successfully matches produces an answer. -/
theorem spaceMatch_complete (s : PeTTaSpace) (pat tmpl : Pattern)
    (atom : Pattern) (bs : Bindings)
    (hatom : atom ∈ s.storedAtoms) (hbs : bs ∈ matchPattern pat atom) :
    applyBindings bs tmpl ∈ spaceMatch s pat tmpl := by
  unfold spaceMatch
  rw [List.mem_flatMap]
  exact ⟨atom, hatom, List.mem_map.mpr ⟨bs, hbs, rfl⟩⟩

/-- `spaceMatch` on an empty space yields no answers. -/
@[simp]
theorem spaceMatch_empty (pat tmpl : Pattern) :
    spaceMatch PeTTaSpace.empty pat tmpl = [] := by
  rfl

/-- Membership characterization for `spaceMatch`. -/
theorem mem_spaceMatch {s : PeTTaSpace} {pat tmpl q : Pattern} :
    q ∈ spaceMatch s pat tmpl ↔
    ∃ atom ∈ s.storedAtoms, ∃ bs ∈ matchPattern pat atom, q = applyBindings bs tmpl :=
  ⟨spaceMatch_sound s pat tmpl q, fun ⟨atom, ha, bs, hbs, heq⟩ =>
    heq ▸ spaceMatch_complete s pat tmpl atom bs ha hbs⟩

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

/-- Existing stored atoms stay visible after adding an ordinary fact. -/
theorem mem_storedAtoms_addAtom {s : PeTTaSpace} {p atom : Pattern}
    (h : atom ∈ s.storedAtoms) :
    atom ∈ (s.addAtom p).storedAtoms := by
  unfold storedAtoms at h ⊢
  simp [addAtom] at h ⊢
  exact Or.inr h

/-- Any fact stored in the space is also a visible stored atom. -/
theorem mem_storedAtoms_of_fact {s : PeTTaSpace} {fact : Pattern}
    (h : fact ∈ s.facts) :
    fact ∈ s.storedAtoms := by
  unfold storedAtoms
  exact List.mem_append_left _ h

/-- Any premise-free stored rule contributes its surface `(= lhs rhs)` atom to
the stored-atom query view. -/
theorem mem_storedAtoms_of_premiseFreeRule
    {s : PeTTaSpace} {r : RewriteRule}
    (hr : r ∈ s.rules) (hprem : r.premises = []) :
    .apply "=" [r.left, r.right] ∈ s.storedAtoms := by
  unfold storedAtoms storedRuleAtoms
  apply List.mem_append_right
  rw [List.mem_filterMap]
  refine ⟨r, hr, ?_⟩
  simp [storedRuleAtom?, hprem]

/-- Removing an atom from the visible stored-atom layer only removes that atom
from the current stored-atom view. -/
theorem mem_storedAtoms_removeAtom_subset {s : PeTTaSpace} {p atom : Pattern}
    (h : atom ∈ (s.removeAtom p).storedAtoms) :
    atom ∈ s.storedAtoms := by
  unfold storedAtoms storedRuleAtoms at h ⊢
  rw [List.mem_append] at h ⊢
  rcases h with hfact | hrule
  · exact Or.inl (mem_facts_removeAtom_subset hfact)
  · right
    rw [List.mem_filterMap] at hrule ⊢
    rcases hrule with ⟨r, hr, hstored⟩
    refine ⟨r, ?_, hstored⟩
    simp [removeAtom] at hr
    exact hr.1

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

end Mettapedia.Languages.MeTTa.PeTTa
