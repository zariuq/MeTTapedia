import Mathlib.Data.List.Basic
import Mettapedia.GSLT.Core.Composition

/-!
# Certified finite rule indexing

This module isolates a generic lowering for authored rule systems whose rules
have a statically recoverable dispatch key.  Typical keys are an outer
constructor together with its arity, but the construction does not depend on
the meaning of keys or rules.

Admission is local and decidable: every rule must expose a key.  Accepted
rules are grouped into order-preserving buckets.  The main theorem proves that
looking up a compiled bucket returns exactly the source rules selected by a
full scan.  A rule with no recognized key is rejected rather than placed in a
fallback bucket.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation

universe uKey uRule

variable {Key : Type uKey} {Rule : Type uRule}

/-- A compact rule index represented as distinct key buckets.  Concrete
backends may further lower this abstract artifact to hashing or dense slots. -/
abbrev BucketIndex (Key : Type uKey) (Rule : Type uRule) :=
  List (Key × List Rule)

/-- Retrieve the bucket for a query key. -/
def lookup [DecidableEq Key] (query : Key) :
    BucketIndex Key Rule → List Rule
  | [] => []
  | (key, rules) :: rest =>
      if query = key then rules else lookup query rest

/-- Add one rule to its bucket.  Rules are inserted while traversing the
source inventory from right to left, so every bucket retains source order. -/
def insert [DecidableEq Key] (key : Key) (rule : Rule) :
    BucketIndex Key Rule → BucketIndex Key Rule
  | [] => [(key, [rule])]
  | (stored, rules) :: rest =>
      if stored = key then
        (stored, rule :: rules) :: rest
      else
        (stored, rules) :: insert key rule rest

/-- Inserting a rule changes exactly the queried bucket. -/
theorem lookup_insert [DecidableEq Key]
    (query key : Key) (rule : Rule) (index : BucketIndex Key Rule) :
    lookup query (insert key rule index) =
      if query = key then rule :: lookup query index
      else lookup query index := by
  induction index with
  | nil =>
      by_cases same : query = key <;> simp [insert, lookup, same]
  | cons entry rest ih =>
      obtain ⟨stored, rules⟩ := entry
      by_cases storedKey : stored = key
      · subst key
        by_cases queryStored : query = stored <;>
          simp [insert, lookup, queryStored]
      · by_cases queryStored : query = stored
        · simp [insert, lookup, storedKey, queryStored]
        · simp [insert, lookup, storedKey, queryStored, ih]

/-- Source semantics: scan every rule and retain precisely those whose
recognized key equals the query. -/
def sourceCandidates [DecidableEq Key]
    (keyOf? : Rule → Option Key) (rules : List Rule) (query : Key) :
    List Rule :=
  rules.filter (fun rule => keyOf? rule == some query)

/-- Partial index compiler.  A missing key is an admission failure; accepted
rules are grouped into source-order buckets. -/
def compile? [DecidableEq Key] (keyOf? : Rule → Option Key) :
    List Rule → Option (BucketIndex Key Rule)
  | [] => some []
  | rule :: rules =>
      match keyOf? rule with
      | none => none
      | some key =>
          match compile? keyOf? rules with
          | none => none
          | some index => some (insert key rule index)

/-- Executable local recognizer for the indexable fragment. -/
def supported? (keyOf? : Rule → Option Key) (rules : List Rule) : Bool :=
  rules.all (fun rule => (keyOf? rule).isSome)

/-- The compiler succeeds exactly on the fragment accepted by the local
recognizer. -/
theorem compile?_isSome_eq_supported? [DecidableEq Key]
    (keyOf? : Rule → Option Key) (rules : List Rule) :
    (compile? keyOf? rules).isSome = supported? keyOf? rules := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      cases keyEq : keyOf? rule with
      | none => simp [compile?, supported?, keyEq]
      | some key =>
          cases tailEq : compile? keyOf? rules <;>
            simp_all [compile?, supported?]

/-- Complete observation theorem for compiled dispatch.  It preserves not
only membership but the exact source order and multiplicity of candidates. -/
theorem lookup_compile?_eq_sourceCandidates [DecidableEq Key]
    (keyOf? : Rule → Option Key) (rules : List Rule)
    (index : BucketIndex Key Rule)
    (accepted : compile? keyOf? rules = some index) (query : Key) :
    lookup query index = sourceCandidates keyOf? rules query := by
  induction rules generalizing index with
  | nil =>
      simp [compile?] at accepted
      subst index
      rfl
  | cons rule rules ih =>
      cases keyEq : keyOf? rule with
      | none => simp [compile?, keyEq] at accepted
      | some key =>
          cases tailEq : compile? keyOf? rules with
          | none => simp [compile?, keyEq, tailEq] at accepted
          | some tail =>
              simp [compile?, keyEq, tailEq] at accepted
              subst index
              rw [lookup_insert]
              rw [ih tail tailEq]
              by_cases same : query = key
              · subst query
                simp [sourceCandidates, keyEq]
              · have reverse : key ≠ query := Ne.symm same
                simp [sourceCandidates, keyEq, same, reverse]

/-- An admitted source inventory carries the exact result of the partial
index compiler. -/
structure AdmittedProgram (Key : Type uKey) (Rule : Type uRule)
    [DecidableEq Key] (keyOf? : Rule → Option Key) where
  source : List Rule
  compiled : BucketIndex Key Rule
  compile_eq : compile? keyOf? source = some compiled

/-- Run admission and retain the compiler equation. -/
def admitProgram [DecidableEq Key] (keyOf? : Rule → Option Key)
    (source : List Rule) : Option (AdmittedProgram Key Rule keyOf?) :=
  match accepted : compile? keyOf? source with
  | none => none
  | some compiled => some { source, compiled, compile_eq := accepted }

/-- Admission succeeds exactly when the underlying partial compiler does. -/
theorem admitProgram_isSome_eq_compile? [DecidableEq Key]
    (keyOf? : Rule → Option Key) (source : List Rule) :
    (admitProgram keyOf? source).isSome = (compile? keyOf? source).isSome := by
  unfold admitProgram
  split <;> simp_all

/-- Rule indexing as a composable computed realization. -/
def indexedDispatchRealization [DecidableEq Key]
    (keyOf? : Rule → Option Key) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedProgram Key Rule keyOf?)
      (BucketIndex Key Rule)
      (Key → List Rule) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted => sourceCandidates keyOf? admitted.source
  observeArtifact := fun _ index query => lookup query index
  adequate := by
    intro _ admitted
    funext query
    exact lookup_compile?_eq_sourceCandidates keyOf? admitted.source
      admitted.compiled admitted.compile_eq query

/-! ## Cross-shape and rejection canaries -/

private inductive Pattern where
  | application (head : String) (arity : Nat)
  | headless (name : String)
deriving DecidableEq

private structure SymbolicRule where
  name : String
  pattern : Pattern
deriving DecidableEq

private def symbolicKey? (rule : SymbolicRule) : Option (String × Nat) :=
  match rule.pattern with
  | .application head arity => some (head, arity)
  | .headless _ => none

private def relationRules : List SymbolicRule :=
  [{ name := "edge-left", pattern := .application "edge" 2 },
   { name := "node", pattern := .application "node" 1 },
   { name := "edge-right", pattern := .application "edge" 2 }]

/-- A symbolic head-and-arity inventory is admitted and retains the order of
two rules in the same bucket. -/
  example :
    ∃ index, compile? symbolicKey? relationRules = some index ∧
      lookup ("edge", 2) index = [relationRules[0], relationRules[2]] := by
  exact ⟨[(("edge", 2), [relationRules[0], relationRules[2]]),
      (("node", 1), [relationRules[1]])],
    by decide, by decide⟩

/-- The same compiler accepts a distinct numeric opcode inventory. -/
example :
    compile? (fun opcode : Nat => some (opcode % 2)) [10, 12, 11] =
      some [(1, [11]), (0, [10, 12])] := by
  decide

/-- A headless rule is rejected rather than hidden in a catch-all bucket. -/
example :
    (compile? symbolicKey?
      [{ name := "dynamic", pattern := .headless "variable" }]).isSome =
        false := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation
