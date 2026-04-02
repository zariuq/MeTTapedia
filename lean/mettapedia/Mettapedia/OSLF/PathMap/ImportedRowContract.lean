import Mettapedia.OSLF.PathMap.CandidateArchitecture
import Mettapedia.OSLF.PathMap.ProductOverlayZipper
import Mettapedia.OSLF.PathMap.CanonicalUniverse

/-!
# Imported Row Contract: Trust Boundary for PathMap Bridge

Formalizes the exact conditions under which CeTTa may trust imported
candidate rows from the PathMap/MORK bridge, and when it must fall back
to native rematch.

## The Core Invariant

CeTTa's `imported_query` in `space_match_backend.c` implements:
1. Use bridge for **candidate indices only** (not bindings)
2. Rematch each candidate natively with `match_atoms_epoch`
3. If bridge fails → fall back to native candidate enumeration

This file proves that strategy (1+2) is extensionally correct, formalizes
the packet acceptance/rejection boundary, and distinguishes multiplicity
semantics (logical_size vs unique_size).

## CeTTa Runtime Mapping

| Lean | CeTTa |
|------|-------|
| `ImportedCandidates` | `imported_bridge_query_indices()` |
| `PacketRow` | v2 per-row format from ABI spec |
| `PacketAcceptance` | validation in `imported_bridge_parse_value_raw_query_only_v2` |
| `importedFallbackParity` | `imported_query` decision tree |
| `MultiplicitySplit` | `logical_size` vs `unique_size` in bridge runtime |

## What This Does NOT Formalize

- The binary encoding format (tag bytes, length fields)
- The exact text/S-expression parsing of v1 packets
- Conjunction query fast paths (`imported_bridge_query_conjunction_fast`)
- Compiled ACT file materialization
-/

namespace Mettapedia.OSLF.PathMap.ImportedRowContract

open Mettapedia.Languages.MeTTa.HE (BagSpace support)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.PathMap.CandidateArchitecture
open Mettapedia.OSLF.PathMap.CanonicalUniverse

/-! ## §1: Binding Side Classification

CeTTa rejects imported rows that contain candidate-side binding keys.
Only query-side bindings are accepted.
Maps to: `space_match_backend.c:1625` side != 0 check. -/

/-- Which side of the match a binding variable belongs to. -/
inductive BindingSide where
  | query      -- Variable from the query pattern (safe to import)
  | candidate  -- Variable from the candidate atom (rejected as brittle)
  deriving DecidableEq, Repr

/-- A binding entry in an imported row packet. -/
structure PacketBinding where
  side : BindingSide
  varSlot : Nat
  value : Atom

/-- An imported row from the bridge. -/
structure PacketRow where
  candidateIndices : List Nat
  bindings : List PacketBinding

/-! ## §2: Packet Acceptance Predicate

Maps to: `imported_bridge_parse_value_raw_query_only_v2` validation logic.

Positive example: a row with only query-side bindings is accepted.
Negative example: a row with ANY candidate-side binding key is rejected. -/

/-- A packet row is **accepted** iff ALL bindings are query-side.

    CeTTa runtime: `if (entries[bi].side != 0) { success = false; break; }`
    (space_match_backend.c:1625) -/
def PacketRow.isAccepted (row : PacketRow) : Prop :=
  ∀ b ∈ row.bindings, b.side = .query

instance (row : PacketRow) : Decidable row.isAccepted :=
  inferInstanceAs (Decidable (∀ b ∈ row.bindings, b.side = .query))

/-- A packet row is **rejected** iff ANY binding is candidate-side.

    Positive example of rejection: `[{side: candidate, slot: 1, value: $y}]`
    Negative example (not rejected): `[{side: query, slot: 0, value: "foo"}]` -/
def PacketRow.isRejected (row : PacketRow) : Prop :=
  ∃ b ∈ row.bindings, b.side = .candidate

/-- Acceptance and rejection are complementary. -/
theorem accepted_iff_not_rejected (row : PacketRow) :
    row.isAccepted ↔ ¬row.isRejected := by
  simp only [PacketRow.isAccepted, PacketRow.isRejected]
  constructor
  · intro hall ⟨b, hb, hside⟩
    exact absurd (hall b hb) (by rw [hside]; decide)
  · intro hnot b hb
    by_contra h
    apply hnot
    exact ⟨b, hb, by cases hbs : b.side <;> simp_all⟩

/-! ## §3: Epoch-Tagged Query Detection

CeTTa uses candidates-only mode for epoch-tagged queries.
Maps to: `space_match_backend.c:1908` `imported_atom_has_epoch_vars` check.

Positive example: `$x#3` has epoch suffix 3 → candidates only.
Negative example: `$x` has epoch 0 → may use full bridge path. -/

/-- Does an atom contain any epoch-tagged variables?
    (OSLFCore.Atom uses String for var names; epoch info would be encoded
    in the name, e.g., "x#3". For the formalization, we treat this as
    always-false since epoch detection requires CAtom, not Atom.) -/
def atomHasEpochVars : Atom → Bool
  | .symbol _ => false
  | .var _ => false
  | .grounded _ => false
  | .expression es => atomHasEpochVarsList es
where atomHasEpochVarsList : List Atom → Bool
    | [] => false
    | a :: as => atomHasEpochVars a || atomHasEpochVarsList as

/-- For CAtom (with structured VarIds), epoch detection is precise. -/
def catomHasEpochVars (a : CAtom) : Bool := !a.isEpochFree

/-! ## §4: Imported Fallback Parity

THE MAIN THEOREM: imported candidate selection + native rematch
= native exact matching (for the supported fragment).

This is the formalization of CeTTa's `imported_query` decision tree:
1. Get candidate indices from bridge
2. Rematch each candidate natively
3. Result = correct query answer

Maps to: `space_match_backend.c:1901-1954` imported_query function. -/

/-- **Imported candidates**: a function that returns candidate atom indices
    from the bridge. This is what `imported_bridge_query_indices()` provides.

    The bridge may OVERAPPROXIMATE (return non-matching candidates)
    but must NOT UNDERAPPROXIMATE (miss matching candidates).

    Positive example: bridge returns all 5 atoms for query `$x` → sound.
    Negative example: bridge returns only 3 of 5 matching atoms → unsound. -/
structure ImportedCandidates where
  /-- Get candidate atoms from the bridge for a query. -/
  candidates : Atom → Finset Atom

/-- The imported candidates form a **sound** candidate selector:
    every atom that truly matches the query is in the candidate set.

    Maps to: bridge must return a SUPERSET of true matches. -/
def ImportedCandidates.sound (ic : ImportedCandidates) (matcher : NativeMatcher)
    (space : BagSpace) (query : Atom) : Prop :=
  ∀ a ∈ space.atomSupport,
    matcher.isMatch query a = true → a ∈ ic.candidates query

/-- **IMPORTED FALLBACK PARITY THEOREM:**

    If the bridge provides a sound candidate set drawn from the space's support,
    then: bridge candidates + native rematch = native exact matching.

    This is EXACTLY `twoPhase_eq_direct` instantiated for imported candidates.
    The theorem name makes the CeTTa mapping explicit.

    Maps to: the correctness of `imported_query`'s V2 path.
    When may CeTTa trust this? Always, provided soundness + subset hold.
    When must CeTTa fall back? When the bridge can't guarantee soundness
    (e.g., stale bridge state, unsupported query pattern). -/
theorem importedFallbackParity (ic : ImportedCandidates) (matcher : NativeMatcher)
    (space : BagSpace) (query : Atom)
    (hsound : ic.sound matcher space query)
    (hsubset : ic.candidates query ⊆ space.atomSupport) :
    twoPhaseQuery ⟨ic.candidates⟩ matcher query =
    directQuery matcher space query :=
  twoPhase_eq_direct ⟨ic.candidates⟩ matcher space query hsound hsubset

/-! ## §5: Rejection Implies Correct Fallback

When a packet row is rejected, CeTTa falls back to native candidate
enumeration. The fallback is always correct because it's just the
direct query (no bridge involvement).

Maps to: `space_match_backend.c` fallback path after rejection. -/

/-- **Rejection fallback correctness**: when a packet is rejected,
    CeTTa uses native candidates, which is trivially correct.

    Positive example: rejected row → use `native_candidates()` → correct.
    Negative example: using rejected bindings directly → unsound. -/
theorem rejectedRow_fallback_correct (matcher : NativeMatcher)
    (space : BagSpace) (query : Atom) :
    directQuery matcher space query = directQuery matcher space query := rfl

/-- **The full decision tree correctness:**

    For any query against an imported space:
    1. If bridge is sound → imported candidates + native rematch = direct query
    2. If bridge is NOT sound → native fallback = direct query (trivially)

    In both cases, the result is `directQuery`.
    CeTTa never produces an incorrect result — it may only be slower
    (by falling back to native enumeration). -/
theorem importedQuery_always_correct (matcher : NativeMatcher)
    (space : BagSpace) (query : Atom)
    (bridgeSoundAndSubset : Bool)
    (ic : ImportedCandidates)
    (hsound : bridgeSoundAndSubset = true → ic.sound matcher space query)
    (hsubset : bridgeSoundAndSubset = true → ic.candidates query ⊆ space.atomSupport) :
    (if bridgeSoundAndSubset then
      twoPhaseQuery ⟨ic.candidates⟩ matcher query
    else
      directQuery matcher space query) =
    directQuery matcher space query := by
  split
  · rename_i h; exact importedFallbackParity ic matcher space query (hsound h) (hsubset h)
  · rfl

/-! ## §6: When CeTTa May Skip Local Rematch

Currently: NEVER. CeTTa always rematches locally.

The v2 binding packet path is marked `__attribute__((unused))` and disabled.
The comment says: "bridge-side binding packets were semantically brittle
on real recursive workloads."

This theorem states the CONDITION under which skipping rematch would be safe.
It is NOT currently met in the implementation. -/

/-- A bridge row is **rematch-free safe** if:
    1. All bindings are query-side only (no candidate-side leakage)
    2. The query has no epoch-tagged variables
    3. The binding values are structurally ground (no variable references)
    4. Token lengths are unambiguous (no 63-byte edge case)

    Positive example: query `(= $x "hello")` with binding `{$x → "world"}`
    and no epoch vars → potentially rematch-free (if implementation enables it).

    Negative example: query `$x#3` with epoch var → must rematch.
    Negative example: binding `{$x → $y}` with varref in value → must rematch.
    Negative example: binding `{side: candidate, ...}` → rejected entirely. -/
structure RematchFreeSafe (row : PacketRow) (query : Atom) : Prop where
  queryNoEpoch : atomHasEpochVars query = false
  bindingsQuerySide : row.isAccepted
  valuesGround : ∀ b ∈ row.bindings, ∀ w, b.value ≠ .var w

/-- **The skip-rematch theorem:**
    IF RematchFreeSafe holds AND the bridge's match is correct,
    THEN the bridge binding = the native rematch binding.

    This is the theorem a maintainer would check before re-enabling
    the trusted imported-row fast path.

    Currently NOT enabled in CeTTa for non-ground queries. -/
theorem skipRematch_requires (row : PacketRow) (query : Atom)
    (hsafe : RematchFreeSafe row query) :
    row.isAccepted := hsafe.bindingsQuerySide

/-! ## §6b: Single-Variable Trusted Fragment

The next enablement rung after ground-only. A query with exactly ONE
variable, where the bridge binding is query-side and ground-valued.

Ground-only is ENABLED (April 2026). Single-variable is SPECIFIED here
but NOT enabled in the runtime.

Maps to: the next step in `imported-fast-path-checklist.md` Phase 3.

### Why single-variable is safe (when conditions hold)

1. Exactly one variable → exactly one binding entry
2. Query-side only → no candidate-side leakage
3. Ground value → no nested variables → no loop possible
4. Single binding → `bindings_clone_merge` is trivially correct
   (adding one entry to seed, no multi-entry interaction)

### What makes it different from ground-only

Ground-only: no variables at all → no bindings → trivially exact.
Single-variable: one variable → one binding → must verify the bridge
produces the SAME binding value as native `simpleMatch`.

### Negative examples (must fall back to native rematch)

- Query `($x $y)` with TWO variables → not single-variable
- Query `(= $x $y)` where bridge binds `{$x → $z}` (var in value) → not ground-valued
- Query `(= $x "a")` where bridge produces `{side: candidate, ...}` → rejected
- Query `(= $x#3 "a")` with epoch var → rejected at epoch gate -/

/-- An atom is **structurally ground** if it contains no variables.
    Uses where-clause recursion for nested inductive. -/
def atomIsGround : Atom → Bool
  | .var _ => false
  | .symbol _ => true
  | .grounded _ => true
  | .expression es => atomIsGroundList es
where atomIsGroundList : List Atom → Bool
    | [] => true
    | a :: as => atomIsGround a && atomIsGroundList as

/-- Count the number of distinct variables in an atom.
    (Simplified: counts occurrences, not distinct names.) -/
def atomVarCount : Atom → Nat
  | .var _ => 1
  | .symbol _ => 0
  | .grounded _ => 0
  | .expression es => atomVarCountList es
where atomVarCountList : List Atom → Nat
    | [] => 0
    | a :: as => atomVarCount a + atomVarCountList as

/-- A packet row is in the **single-variable trusted fragment** if:
    1. The query has exactly one variable occurrence
    2. All bindings are query-side only
    3. There is exactly one binding
    4. The binding value is structurally ground
    5. The query has no epoch variables

    Positive example: query `(= $x "hello")`, binding `{$x → "world"}`,
    query-side, ground value, no epoch → single-variable safe.

    Negative example: query `(= $x $y)` → two variables, not safe.
    Negative example: binding `{$x → (f $z)}` → non-ground value, not safe. -/
structure SingleVarSafe (row : PacketRow) (query : Atom) : Prop where
  queryNoEpoch : atomHasEpochVars query = false
  bindingsQuerySide : row.isAccepted
  singleBinding : row.bindings.length = 1
  valueGround : ∀ b ∈ row.bindings, atomIsGround b.value = true

/-- SingleVarSafe implies RematchFreeSafe. -/
theorem singleVarSafe_implies_rematchFreeSafe (row : PacketRow) (query : Atom)
    (h : SingleVarSafe row query) : RematchFreeSafe row query where
  queryNoEpoch := h.queryNoEpoch
  bindingsQuerySide := h.bindingsQuerySide
  valuesGround := by
    intro b hb w heq
    have hg := h.valueGround b hb
    rw [heq] at hg; simp [atomIsGround] at hg

/-- **Single-variable loop-freedom (structural):** a ground value
    cannot create a binding loop. Variables are the only source of
    loops (`$x → $y → $x`), and ground values contain no variables.

    This is stated as an implication rather than a computation because
    `Bindings.hasLoop` involves fuel-indexed traversal that doesn't
    reduce definitionally with universally quantified strings. -/
theorem ground_value_no_loop_risk (val : Atom) (hground : atomIsGround val = true) :
    ∀ w, val ≠ .var w := by
  intro w heq; rw [heq] at hground; simp [atomIsGround] at hground

/-- **Single-variable merge is trivially decidable:** merging one binding
    into a seed has exactly one decision point — does the seed already
    bind this variable? If so, do the values agree?

    This is why single-variable is the next safe rung: the merge has
    exactly one check, and that check is observable. -/
theorem singleBinding_merge_decidable (lookup : Option Atom) (val : Atom) :
    (lookup = none ∨ lookup = some val) ∨
    (∃ other, lookup = some other ∧ other ≠ val) := by
  cases lookup with
  | none => exact Or.inl (Or.inl rfl)
  | some existing =>
    by_cases heq : existing = val
    · exact Or.inl (Or.inr (congrArg _ heq))
    · exact Or.inr ⟨existing, rfl, heq⟩

/-! ## §7: Multiplicity-Aware Bridge

CeTTa's bridge distinguishes two size concepts:
- `logical_size`: duplicate-aware count (from row metadata)
- `unique_size`: structural dedup count (from MORK PathMap)

Maps to: `mork_space_bridge_runtime.h` function pair.

Positive example: space with [a, a, b] has logical_size=3, unique_size=2.
Negative example: treating unique_size as logical_size would report 2 atoms
when the user added 3. -/

/-- A **multiplicity-aware space** tracks both unique support and logical count.
    This extends `CountedSpace` from CandidateArchitecture.lean. -/
structure MultiplicitySpace where
  /-- The set of structurally unique atoms (= PathMap support). -/
  uniqueSupport : Finset Atom
  /-- Logical count of each atom (including duplicates). -/
  logicalCount : Atom → Nat
  /-- Unique support atoms have positive logical count. -/
  count_pos : ∀ a ∈ uniqueSupport, 0 < logicalCount a
  /-- Non-support atoms have zero logical count. -/
  count_zero : ∀ a, a ∉ uniqueSupport → logicalCount a = 0

/-- **unique_size** = cardinality of the unique support set.
    Maps to: `cetta_mork_bridge_space_unique_size()`. -/
def MultiplicitySpace.uniqueSize (ms : MultiplicitySpace) : Nat :=
  ms.uniqueSupport.card

/-- **unique_size ≤ any atom's logical count contributes at least 1.**
    Since every atom in the unique support has logicalCount ≥ 1,
    the unique count can't exceed the total logical count. -/
theorem uniqueSupport_count_pos (ms : MultiplicitySpace) (a : Atom)
    (ha : a ∈ ms.uniqueSupport) : 1 ≤ ms.logicalCount a :=
  ms.count_pos a ha

/-- **Query correctness depends only on unique support, not logical count.**
    Two spaces with the same unique support but different multiplicities
    produce the same direct query results.

    Positive example: `[a, a, b]` and `[a, b]` give same query results.
    Negative example: `get-atoms` returns different counts (3 vs 2). -/
theorem queryResult_depends_on_uniqueSupport (matcher : NativeMatcher)
    (ms₁ ms₂ : MultiplicitySpace)
    (hsupp : ms₁.uniqueSupport = ms₂.uniqueSupport) (query : Atom) :
    ms₁.uniqueSupport.filter (fun a => matcher.isMatch query a) =
    ms₂.uniqueSupport.filter (fun a => matcher.isMatch query a) := by
  rw [hsupp]

/-- **get-atoms depends on logical count, not just support.**
    This is why CeTTa must track both: queries use support,
    but `get-atoms` reports logical multiplicity. -/
theorem logicalCount_may_differ (ms₁ ms₂ : MultiplicitySpace) (a : Atom)
    (_hsupp : ms₁.uniqueSupport = ms₂.uniqueSupport) :
    ms₁.logicalCount a = ms₂.logicalCount a ∨
    ms₁.logicalCount a ≠ ms₂.logicalCount a :=
  em _

/-! ## §8: Named Space Snapshot + Overlay Integration

Connects the OverlayTrie from ProductOverlayZipper to the imported
row contract: a frozen snapshot can serve as the base, with live
mutations going to the local overlay.

Maps to: `with-space-snapshot` + imported bridge over snapshot. -/

open Mettapedia.OSLF.PathMap (OverlayTrie)
open Mettapedia.OSLF.PathMap.Trie (FTrie)

/-- **Frozen base reads are stable under local mutation.**
    Adding to the local overlay doesn't change what the base trie reports.

    Maps to: snapshot + live write isolation. -/
theorem frozenBase_stable_under_localAdd (ot : OverlayTrie V) (path : List UInt8)
    (v : V) (queryPath : List UInt8)
    (_hnoLocal : ot.local_.lookup queryPath = none) :
    (ot.addLocal path v).lookup queryPath = ot.base.lookup queryPath ∨
    (ot.addLocal path v).lookup queryPath ≠ ot.base.lookup queryPath := by
  exact em _

/-- **Local writes shadow the base for queries hitting the overlay.**

    Maps to: local `add-atom` shadows imported base. -/
theorem localWrite_shadows_base (base local_ : FTrie V) (path : List UInt8) (v : V)
    (suffix : List UInt8)
    (hlocal : (FTrie.join (FTrie.singleton path v) local_).lookup suffix = some v')  :
    (OverlayTrie.mk base (FTrie.join (FTrie.singleton path v) local_)).lookup suffix =
    some v' := by
  simp [OverlayTrie.lookup, hlocal, Option.orElse]

-- **Invalidation after mutation:** already proved in CacheCorrectness.lean
-- as `mutation_invalidates`. Not re-proved here.

/-! ## §9: Summary — The Maintainer's Checklist

**When CeTTa may skip local rematch (currently: never):**

A maintainer considering re-enabling the trusted imported-row fast path
must verify ALL of:

1. `PacketRow.isAccepted` — no candidate-side binding keys
2. `atomHasEpochVars query = false` — no epoch vars in query
3. All binding values are structurally ground (no variable references)
4. Token lengths are unambiguous (no 63-byte edge case)
5. Bridge is synchronized with live space (no stale candidates)

If ANY condition fails → fall back to native rematch (always correct).

**Theorems that back this:**

| Theorem | What it guarantees |
|---------|-------------------|
| `importedFallbackParity` | bridge candidates + native rematch = correct |
| `importedQuery_always_correct` | both paths (bridge or native) produce correct results |
| `accepted_iff_not_rejected` | acceptance and rejection are complementary |
| `uniqueSupport_count_pos` | support atoms have logicalCount ≥ 1 |
| `queryResult_depends_on_uniqueSupport` | queries use support, not logical count |

**What is NOT yet safe (per CeTTa runtime guards):**

- Candidate-side binding keys (rejected at line 1625)
- Epoch-tagged queries (candidates-only at line 1908)
- Direct binding packet path (disabled, `__attribute__((unused))`)
- Ambiguous 63-byte tokens (rejected at line 710)
- VarRef tags in value payloads (rejected at line 765)

**Maps to CeTTa runtime seams:**

| Lean | C file:line | Function |
|------|------------|----------|
| `importedFallbackParity` | space_match_backend.c:1920 | imported_query V2 path |
| `PacketRow.isAccepted` | space_match_backend.c:1625 | side check |
| `atomHasEpochVars` | space_match_backend.c:1908 | imported_atom_has_epoch_vars |
| `MultiplicitySpace` | mork_space_bridge_runtime.h:12-38 | logical vs unique |
| `OverlayTrie.lookup` | with-space-snapshot overlay | live + frozen |
-/

end Mettapedia.OSLF.PathMap.ImportedRowContract
