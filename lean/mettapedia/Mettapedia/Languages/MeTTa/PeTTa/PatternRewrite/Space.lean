import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Answers
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.MatchSpec

open Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite (RewriteResults)

/-!
# PeTTa atomspaces and selected rewriting over Pattern

This module retains the selected Pattern rewrite view used by older PeTTa
consumers. Its historical source encoding maps a bare symbol and a nullary
expression to the same `Pattern`, and maps numbers to symbols.
`PeTTaEval` selects one rule rewrite or one query; a selected right-hand
side is not a completed program answer. The semantics of PeTTa programs is
stated over `OSLFCore.Atom` in `SpaceSemantics`, `Effects`, `StdLib` and
`Eval`.

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

/-- Append an atom in insertion order, retaining duplicate occurrences. -/
def addAtom (s : PeTTaSpace) (p : Pattern) : PeTTaSpace :=
  { s with facts := s.facts ++ [p] }

 /-- Stored source atom corresponding to a premise-free rewrite rule.

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
def spaceMatch (s : PeTTaSpace) (pat tmpl : Pattern) : RewriteResults :=
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
  List.mem_append_left _ h

/-- The added atom is a fact in the new space. -/
theorem mem_facts_addAtom_self (s : PeTTaSpace) (p : Pattern) :
    p ∈ (s.addAtom p).facts :=
  List.mem_append_right _ (List.mem_cons_self)

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
  rcases List.mem_append.mp h with oldFact | storedRule
  · exact List.mem_append_left _ (List.mem_append_left _ oldFact)
  · exact List.mem_append_right _ storedRule

/-- Any fact stored in the space is also a visible stored atom. -/
theorem mem_storedAtoms_of_fact {s : PeTTaSpace} {fact : Pattern}
    (h : fact ∈ s.facts) :
    fact ∈ s.storedAtoms := by
  unfold storedAtoms
  exact List.mem_append_left _ h

/-- Any premise-free stored rule contributes its interface `(= lhs rhs)` atom to
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
- `spaceMatch s pat tmpl : RewriteResults` — models MeTTa's `(match &self pat tmpl)`
- `spaceMatch_sound` — every answer comes from a matching fact
- `spaceMatch_complete` — every match produces an answer
- `mem_spaceMatch` — full characterization

### Mutation (pure, returns new space)
- `mem_facts_addAtom`, `mem_facts_addAtom_self` — addAtom preserves/adds facts
- `mem_facts_removeAtom_subset` — removeAtom only removes facts
-/

end Mettapedia.Languages.MeTTa.PeTTa

/-! ## MeTTaIL rewrite view

These Pattern judgments describe selected rewrites and queries. A selected
right-hand side is not a completed recursive program answer.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! ## Pure Evaluation Relation -/

/-- Pure PeTTa evaluation judgment for the type-free fragment.

    `PeTTaEval s p answers` means: in atomspace `s`, expression `p`
    evaluates to the nondeterministic answer set `answers`.

    This is the declarative specification; the operational behavior follows
    from the LP semantics (see `LPSoundness.lean`). -/
inductive PeTTaEval (s : PeTTaSpace) : Pattern → RewriteResults → Prop where

  /-- **Variables**: a free variable (metavariable) evaluates to itself.
      MeTTa spec: `metta(Variable, ...) → [(Variable, bindings)]`. -/
  | var (x : String) :
      PeTTaEval s (.fvar x) [.fvar x]

  /-- **Bound variables**: evaluate to themselves (structurally inert). -/
  | bvar (n : Nat) :
      PeTTaEval s (.bvar n) [.bvar n]

  /-- **Ground atoms** (nullary applications): evaluate to themselves.
      MeTTa spec: `metta(Atom, ...) → [(Atom, bindings)]` when no rule matches. -/
  | ground (c : String) :
      PeTTaEval s (.apply c []) [.apply c []]

  /-- **Rule application (top rule)**: match the LHS of a rule against `p`,
      apply the resulting bindings to the RHS, producing `q`.

      Conditions:
      - `r ∈ s.rules`: the rule is in the atomspace
      - `r.premises = []`: only unconditional rules (no premises)
      - `bs ∈ matchPattern r.left p`: LHS matches `p` with bindings `bs`
      - `applyBindings bs r.right = q`: applying bindings to RHS gives `q`

      MeTTa spec: `metta_call` after a successful `match_atoms`.
      HE MeTTa: `(= lhs rhs)` rules applied via unification.
      PeTTa: top-level Prolog clause `metta_call(lhs, rhs)`. -/
  | ruleApp (r : RewriteRule) (bs : Bindings) (p q : Pattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ matchPattern r.left p)
      (hq : applyBindings bs r.right = q) :
      PeTTaEval s p [q]

  /-- **Space query** (`match &self pat tmpl`): returns all groundings of `tmpl`
      obtained by pattern-matching `pat` against facts in the atomspace.

      Models: `(match &self pat tmpl)` in MeTTa. -/
  | spaceQuery (pat tmpl : Pattern) (results : RewriteResults)
      (hres : results = s.spaceMatch pat tmpl) :
      PeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) results

  /-- **Superpose**: a `superpose` expression evaluates to each alternative.
      The argument must be a vector collection.

      Models: `(superpose (a b c))` → answers `a`, `b`, `c` (nondeterministically).
      PeTTa: Prolog disjunction over alternatives. -/
  | superpose (alts : List Pattern) :
      PeTTaEval s (.apply "superpose" [.collection .vec alts none]) alts

  /-- **Collapse**: collect all answers from a nondeterministic expression into a list.

      If `p` evaluates to `answers`, then `(collapse p)` evaluates to the singleton
      containing the vector collection of all those answers.

      Models: `(collapse p)` in MeTTa / `findall(X, eval(p, X), Xs)` in PeTTa. -/
  | collapse (p : Pattern) (answers : RewriteResults)
      (h : PeTTaEval s p answers) :
      PeTTaEval s (.apply "collapse" [p]) [.collection .vec answers none]

/-! ## Basic Properties -/

/-- The `var` constructor fires directly: fvar always has `[.fvar x]` as a possible answer. -/
theorem petta_eval_var_case (s : PeTTaSpace) (x : String) :
    PeTTaEval s (.fvar x) [.fvar x] :=
  PeTTaEval.var x

/-- Rule application always produces exactly one answer. -/
theorem petta_eval_ruleApp_singleton {s : PeTTaSpace} (r : RewriteRule) (bs : Bindings)
    (p q : Pattern) (hr : r ∈ s.rules) (hprem : r.premises = [])
    (hm : bs ∈ matchPattern r.left p) (hq : applyBindings bs r.right = q) :
    PeTTaEval s p [q] :=
  PeTTaEval.ruleApp r bs p q hr hprem hm hq

/-- Superpose of nil yields empty answers. -/
theorem petta_eval_superpose_nil {s : PeTTaSpace} :
    PeTTaEval s (.apply "superpose" [.collection .vec [] none]) [] :=
  PeTTaEval.superpose []

/-- Collapse always produces a singleton answer (the collection of all inner answers). -/
theorem petta_eval_collapse_singleton {s : PeTTaSpace} {p : Pattern} {answers : RewriteResults}
    (h : PeTTaEval s p answers) :
    ∃ ans, PeTTaEval s (.apply "collapse" [p]) [ans] :=
  ⟨.collection .vec answers none, PeTTaEval.collapse p answers h⟩

/-- The spaceQuery constructor produces exactly the spaceMatch answers. -/
theorem petta_eval_spaceQuery_correct (s : PeTTaSpace) (pat tmpl : Pattern) :
    PeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) (s.spaceMatch pat tmpl) :=
  PeTTaEval.spaceQuery pat tmpl _ rfl

/-- `collapse` composed with the certified `match &self` query returns the
singleton collection of all `spaceMatch` answers.

This is the first direct theorem for the next widening target:
query composition under the existing `collapse` aggregation lane. -/
theorem petta_eval_collapse_spaceQuery (s : PeTTaSpace) (pat tmpl : Pattern) :
    PeTTaEval s
      (.apply "collapse" [.apply "match" [.apply "&self" [], pat, tmpl]])
      [.collection .vec (s.spaceMatch pat tmpl) none] :=
  PeTTaEval.collapse _ _ (petta_eval_spaceQuery_correct s pat tmpl)

/-! ## Monotonicity for spaceMatch -/

/-- **spaceMatch monotone in facts**: adding an ordinary fact only adds answers to `spaceMatch`.
    This is stated directly on `spaceMatch` (which is a function, not an inductive). -/
theorem spaceMatch_mono_addAtom (s : PeTTaSpace) (pat tmpl : Pattern) (newFact : Pattern) :
    ∀ q ∈ s.spaceMatch pat tmpl, q ∈ (s.addAtom newFact).spaceMatch pat tmpl := by
  intro q hq
  rw [PeTTaSpace.mem_spaceMatch] at hq ⊢
  obtain ⟨atom, hatom, bs, hbs, heq⟩ := hq
  exact ⟨atom, PeTTaSpace.mem_storedAtoms_addAtom hatom, bs, hbs, heq⟩

/-! ## Summary

**0 sorries. 0 axioms.**

### Inductive Cases
- `var` — fvar evaluates to itself
- `bvar` — bvar evaluates to itself
- `ground` — nullary application evaluates to itself
- `ruleApp` — unconditional rule matching (LHS pattern match → apply RHS)
- `spaceQuery` — `(match &self pat tmpl)` → all groundings of `tmpl`
- `superpose` — `(superpose (a b c))` → alternatives `a`, `b`, `c`
- `collapse` — `(collapse p)` → singleton collection of all `p` answers

### Properties
- `petta_eval_var_case` — var constructor always fires for `.fvar x`
- `petta_eval_ruleApp_singleton` — rule application produces a singleton answer
- `petta_eval_collapse_singleton` — collapse always produces a singleton
- `petta_eval_spaceQuery_results` — spaceQuery returns spaceMatch (or ruleApp override)
- `spaceMatch_mono_addAtom` — spaceMatch is monotone in facts (adding facts only adds answers)

### Note on Nondeterminism
PeTTa is nondeterministic: for a given expression `p`, MULTIPLE constructors may fire
simultaneously. E.g., `.fvar x` can match both `var` AND `ruleApp` (if a rule has LHS
matching variables). `PeTTaEval` captures ALL possible derivations, not just one.
-/

end Mettapedia.Languages.MeTTa.PeTTa

/-! ## Shared-variable selection controls -/

namespace Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace

open Mettapedia.OSLF.MeTTaIL.Syntax

private def friends : PeTTaSpace :=
  { facts := [.apply "friend" [.apply "tim" [], .apply "tom" []],
      .apply "friend" [.apply "tim" [], .apply "bob" []]]
    rules := [] }

private def friendsWithLoop : PeTTaSpace :=
  { facts := [.apply "friend" [.apply "tim" [], .apply "tom" []],
      .apply "friend" [.apply "tim" [], .apply "bob" []],
      .apply "friend" [.apply "bob" [], .apply "bob" []]]
    rules := [] }

/-- A variable occurring twice in the query selects no row whose fields differ. -/
example : friends.spaceMatch (.apply "friend" [.fvar "x", .fvar "x"])
    (.apply "diag" [.fvar "x"]) = [] := by
  decide +kernel

/-- The same query selects exactly the row whose fields are equal. -/
example : friendsWithLoop.spaceMatch (.apply "friend" [.fvar "x", .fvar "x"])
    (.apply "diag" [.fvar "x"]) = [.apply "diag" [.apply "bob" []]] := by
  decide +kernel

/-- A template may repeat a captured variable; selected rows keep their order. -/
example : friends.spaceMatch (.apply "friend" [.apply "tim" [], .fvar "b"])
    (.apply "pair" [.fvar "b", .fvar "b"]) =
      [.apply "pair" [.apply "tom" [], .apply "tom" []],
        .apply "pair" [.apply "bob" [], .apply "bob" []]] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace
