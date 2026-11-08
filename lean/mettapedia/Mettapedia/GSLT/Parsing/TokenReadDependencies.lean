import Mettapedia.GSLT.Parsing.TrieLiteralSelection
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Negative prefix observations for token-table evolution

The query records every prefix bucket of the remaining input, including empty
buckets. Its answer is exactly the existing trie traversal's ordered terminal
occurrences. A later longer token therefore invalidates the certificate even
when the old selected token remains present.

This conservative reference reads beyond a trie's first missing edge. A
compressed edge-walk certificate needs a separate proof. Symbols are generic;
byte decoding, identifier fallback and source positions are adapter obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TokenReadDependencies

open Mettapedia.Machines
open TrieLiteralSelection (Table prefixes bucket build prefixQuery)

variable {Symbol Payload : Type} [DecidableEq Symbol]

abbrev Program (Symbol Payload Answer : Type) :=
  ReadOnlyQuery.Program (List Symbol) (List Payload) Answer

def readPrefixes : List (List Symbol) → Program Symbol Payload (List (Nat × Payload))
  | [] => .pure []
  | word :: rest => .read word fun found =>
      ReadOnlyQuery.bind (readPrefixes rest) fun tail =>
        .pure (found.map (fun payload => (word.length, payload)) ++ tail)

def query (input : List Symbol) : Program Symbol Payload (List (Nat × Payload)) :=
  readPrefixes (prefixes input)

omit [DecidableEq Symbol] in
theorem readPrefixes_answer (store : List Symbol → List Payload) (words : List (List Symbol)) :
    (ReadOnlyQuery.run store (readPrefixes words)).answer =
      words.flatMap (fun word => (store word).map (fun payload => (word.length, payload))) := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp [readPrefixes, ReadOnlyQuery.run, ReadOnlyQuery.run_bind, ih]

omit [DecidableEq Symbol] in
theorem readPrefixes_reads (store : List Symbol → List Payload) (words : List (List Symbol)) :
    (ReadOnlyQuery.run store (readPrefixes words)).reads = ReadOnlyQuery.samples store words := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp [readPrefixes, ReadOnlyQuery.run, ReadOnlyQuery.run_bind,
      ReadOnlyQuery.samples, ih]

/-- The observed program and an independently defined trie traversal have
the same complete ordered prefix matches. -/
theorem query_exact (table : Table Symbol Payload) (input : List Symbol) :
    (ReadOnlyQuery.run (bucket table) (query input)).answer = prefixQuery (build table) input := by
  rw [query, readPrefixes_answer, TrieLiteralSelection.prefixQuery_build]

theorem query_reads (table : Table Symbol Payload) (input : List Symbol) :
    (ReadOnlyQuery.run (bucket table) (query input)).reads =
      ReadOnlyQuery.samples (bucket table) (prefixes input) :=
  readPrefixes_reads _ _

/-- Retain all terminal occurrences at the longest matched prefix. Rule
priority, if desired, is a subsequent explicit selection over this list. -/
def longest (candidates : List (Nat × Payload)) : List (Nat × Payload) :=
  let stop := candidates.foldl (fun best entry => max best entry.1) 0
  candidates.filter fun entry => entry.1 == stop

def validates [DecidableEq Payload] (before after : Table Symbol Payload) (input : List Symbol) : Bool :=
  ReadOnlyQuery.checkReads (bucket after) (ReadOnlyQuery.run (bucket before) (query input)).reads

theorem validated_matches [DecidableEq Payload] (before after : Table Symbol Payload)
    (input : List Symbol) (valid : validates before after input = true) :
    prefixQuery (build after) input = prefixQuery (build before) input := by
  simpa only [query_exact] using
    ReadOnlyQuery.validated_answer (bucket before) (bucket after) (query input) valid

theorem validated_longest [DecidableEq Payload] (before after : Table Symbol Payload)
    (input : List Symbol) (valid : validates before after input = true) :
    longest (prefixQuery (build after) input) = longest (prefixQuery (build before) input) := by
  rw [validated_matches before after input valid]

/-- Adding a word off this input's prefix path preserves all observations. -/
theorem add_nonprefix_validates [DecidableEq Payload] (table : Table Symbol Payload)
    (input word : List Symbol) (payload : Payload) (offPath : ¬ word <+: input) :
    validates table ((word, payload) :: table) input = true := by
  unfold validates
  rw [query_reads, ReadOnlyQuery.checkReads_iff, ReadOnlyQuery.agrees_samples_iff]
  intro prefixWord member
  have different : prefixWord ≠ word := by
    intro same
    apply offPath
    exact same ▸ (TrieLiteralSelection.mem_prefixes input prefixWord).mp member
  simp [bucket, Ne.symm different]

end Mettapedia.GSLT.Parsing.TokenReadDependencies
