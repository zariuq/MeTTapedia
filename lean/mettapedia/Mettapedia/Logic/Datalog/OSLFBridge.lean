import Mettapedia.Logic.Datalog.PathMapBridge
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Datalog ↔ OSLF Bridge

This module connects the Datalog semantics to the OSLF rewrite engine via the
`RelationEnv` interface in `Mettapedia.OSLF.MeTTaIL.Engine`.

## Core idea

The OSLF engine queries relations via `RelationEnv.tuples : String → List Pattern → List (List Pattern)`.
A Datalog `FinInterpretation τ` is a finite set of ground atoms; we can project it into
`RelationEnv` by:

1. **Encoding** each ground constant `c : τ.constants` as `Pattern.apply (toString c) []`.
2. **Encoding** each ground atom `a : GroundAtom τ` as the tuple of encoded args.
3. **Constructing** a `RelationEnv` that, for relation name `rel`, returns all tuples from
   atoms with that relation symbol.

## Key definitions and theorems

- `InjectiveToString` — typeclass asserting that `toString : α → String` is injective
- `constToPattern` — encode a Datalog constant as an OSLF `Pattern`
- `groundAtomArgs` — the argument tuple of a ground atom as `List Pattern`
- `constToPattern_injective` — `constToPattern` is injective under `InjectiveToString`
- `groundAtomArgs_injective` — `groundAtomArgs` is injective (symbol + args) under injectivity
- `datalogToRelEnv` — lift a finite Datalog interpretation to a `RelationEnv`
- `mem_datalogToRelEnv` — correctness: atoms in `I` appear as tuples in the constructed env
- `leastModelRelEnv_complete` — all leastModel atoms appear in the relation environment
- `leastModelRelEnv_sound` — all tuples in the relation environment come from leastModel atoms
-/

namespace Mettapedia.Logic.Datalog

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Section 0: Injective encoding typeclass -/

/-- A typeclass asserting that the `ToString` serialization is injective.
    Required for the Datalog ↔ OSLF bridge to be semantically tight: without
    injectivity, distinct relation symbols (or constants) could map to the same
    `String` key and silently merge. -/
class InjectiveToString (α : Type*) [ToString α] : Prop where
  toString_injective : Function.Injective (toString : α → String)

instance : InjectiveToString String where
  toString_injective := fun _ _ h => h

/-! ## Section 1: Encoding ground atoms as OSLF Patterns -/

/-- Encode a Datalog constant as a zero-argument `Pattern.apply` node. -/
def constToPattern {τ : Signature} [ToString τ.constants] (c : τ.constants) : Pattern :=
  .apply (toString c) []

/-- `constToPattern` is injective under `InjectiveToString`. -/
theorem constToPattern_injective {τ : Signature} [ToString τ.constants]
    [InjectiveToString τ.constants] : Function.Injective (@constToPattern τ _) := by
  intro c c' h
  simp only [constToPattern, Pattern.apply.injEq] at h
  exact InjectiveToString.toString_injective h.1

/-- The argument tuple of a ground atom encoded as OSLF `Pattern`s. -/
def groundAtomArgs {τ : Signature} [ToString τ.constants] (a : GroundAtom τ) : List Pattern :=
  a.atom_terms.map (constToPattern ·)

/-- `groundAtomArgs` is injective (in `atom_terms`) under `InjectiveToString τ.constants`.

    If two atoms have the same symbol and the same encoded argument tuple,
    they are equal.  The symbol hypothesis is required since `groundAtomArgs`
    does not encode the relation symbol. -/
theorem groundAtomArgs_injective {τ : Signature} [ToString τ.constants]
    [InjectiveToString τ.constants]
    {a a' : GroundAtom τ} (hargs : groundAtomArgs a = groundAtomArgs a')
    (hsym : a.symbol = a'.symbol) : a = a' := by
  simp only [groundAtomArgs] at hargs
  have hterms : a.atom_terms = a'.atom_terms :=
    constToPattern_injective.list_map hargs
  exact GroundAtom.ext hsym hterms

/-- The full encoding of a ground atom as a `Pattern.apply` node. -/
def groundAtomToPattern {τ : Signature} [ToString τ.relationSymbols] [ToString τ.constants]
    (a : GroundAtom τ) : Pattern :=
  .apply (toString a.symbol) (groundAtomArgs a)

/-! ## Section 2: Lifting a FinInterpretation to a RelationEnv -/

/-- Construct a `RelationEnv` from a finite Datalog interpretation.

    For each relation name `rel`, returns the argument tuples of all atoms in `I`
    whose relation symbol serializes to `rel`.  The query argument list `qs` is
    ignored here (the OSLF engine's `matchArgs` then handles pattern filtering). -/
noncomputable def datalogToRelEnv {τ : Signature} [ToString τ.relationSymbols] [ToString τ.constants]
    (I : FinInterpretation τ) : RelationEnv where
  tuples rel _ :=
    I.toList.filterMap fun a =>
      if toString a.symbol = rel then some (groundAtomArgs a) else none

/-! ## Section 3: Correctness of the encoding -/

/-- Atoms in `I` appear as tuples in the `datalogToRelEnv I` environment.

    Specifically: if `a ∈ I`, then `groundAtomArgs a` is in
    `(datalogToRelEnv I).tuples (toString a.symbol) qs` for any query args `qs`. -/
theorem mem_datalogToRelEnv {τ : Signature}
    [ToString τ.relationSymbols] [ToString τ.constants]
    (I : FinInterpretation τ) (a : GroundAtom τ) (ha : a ∈ I) (qs : List Pattern) :
    groundAtomArgs a ∈ (datalogToRelEnv I).tuples (toString a.symbol) qs := by
  simp only [datalogToRelEnv]
  apply List.mem_filterMap.mpr
  exact ⟨a, Finset.mem_toList.mpr ha, by simp⟩

/-- Atoms NOT in `I` do not contribute tuples for their own relation-name query.

    More precisely: any tuple `t` in `(datalogToRelEnv I).tuples rel qs` comes from
    some atom in `I` with relation symbol serializing to `rel`. -/
theorem datalogToRelEnv_iff {τ : Signature}
    [ToString τ.relationSymbols] [ToString τ.constants]
    (I : FinInterpretation τ) (rel : String) (qs : List Pattern) (t : List Pattern) :
    t ∈ (datalogToRelEnv I).tuples rel qs ↔
    ∃ a ∈ I, toString a.symbol = rel ∧ t = groundAtomArgs a := by
  simp only [datalogToRelEnv, List.mem_filterMap, Finset.mem_toList]
  constructor
  · rintro ⟨a, ha, ht⟩
    split_ifs at ht with h
    exact ⟨a, ha, h, (Option.some.inj ht).symm⟩
  · rintro ⟨a, ha, hrel, ht⟩
    exact ⟨a, ha, by simp [hrel, ht]⟩

/-! ## Section 4: leastModel as a RelationEnv -/

/-- The least Herbrand model as a `RelationEnv`, given finiteness. -/
noncomputable def leastModelRelEnv {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    [ToString τ.relationSymbols] [ToString τ.constants]
    (kb : KnowledgeBase τ) : RelationEnv :=
  datalogToRelEnv (leastModelFin kb)

/-- EDB facts appear in the leastModel relation environment. -/
theorem leastModelRelEnv_db {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    [ToString τ.relationSymbols] [ToString τ.constants]
    (kb : KnowledgeBase τ) (a : GroundAtom τ) (ha : a ∈ kb.db) (qs : List Pattern) :
    groundAtomArgs a ∈ (leastModelRelEnv kb).tuples (toString a.symbol) qs := by
  apply mem_datalogToRelEnv
  rw [mem_leastModelFin_iff]
  exact leastModel_db kb a ha

/-! ## Section 5: End-to-end bridge soundness and completeness -/

/-- **Completeness**: every atom derivable by Datalog appears in the relation environment.

    For any `a ∈ leastModel kb`, the encoded tuple `groundAtomArgs a` is returned by
    `(leastModelRelEnv kb).tuples (toString a.symbol)` for any query argument list. -/
theorem leastModelRelEnv_complete {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    [ToString τ.relationSymbols] [ToString τ.constants]
    (kb : KnowledgeBase τ) (a : GroundAtom τ) (ha : a ∈ leastModel kb) (qs : List Pattern) :
    groundAtomArgs a ∈ (leastModelRelEnv kb).tuples (toString a.symbol) qs := by
  apply mem_datalogToRelEnv
  rwa [mem_leastModelFin_iff]

/-- **Soundness**: every tuple in the relation environment comes from the least model.

    If `t ∈ (leastModelRelEnv kb).tuples rel qs`, then there is an atom `a ∈ leastModel kb`
    with `toString a.symbol = rel` and `t = groundAtomArgs a`. -/
theorem leastModelRelEnv_sound {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    [ToString τ.relationSymbols] [ToString τ.constants]
    (kb : KnowledgeBase τ) (rel : String) (qs : List Pattern) (t : List Pattern)
    (ht : t ∈ (leastModelRelEnv kb).tuples rel qs) :
    ∃ a ∈ leastModel kb, toString a.symbol = rel ∧ t = groundAtomArgs a := by
  rw [leastModelRelEnv, datalogToRelEnv_iff] at ht
  obtain ⟨a, ha, hrel, heq⟩ := ht
  exact ⟨a, (mem_leastModelFin_iff kb a).mp ha, hrel, heq⟩

end Mettapedia.Logic.Datalog
