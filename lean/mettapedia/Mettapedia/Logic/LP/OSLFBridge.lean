import Mettapedia.Logic.LP.PathMapBridge
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# LP ↔ OSLF Bridge

Port of `Mettapedia.Logic.Datalog.OSLFBridge` onto LP types.

Connects the LP semantics to the OSLF rewrite engine via the `RelationEnv`
interface. In the function-free fragment, LP `GroundAtom` arguments
(`Fin n → GroundTerm σ`) are encoded as `List Pattern` via
`GroundTerm.toConst` + `constToPattern`.

## Key definitions and theorems

- `InjectiveToString` — typeclass asserting `toString` is injective
- `constToPattern` — encode a constant as `Pattern.apply (toString c) []`
- `groundAtomArgs` — the argument tuple of a ground atom as `List Pattern`
- `constToPattern_injective` — `constToPattern` is injective
- `groundAtomArgs_injective` — `groundAtomArgs` + symbol determines atom
- `lpToRelEnv` — lift a finite LP interpretation to a `RelationEnv`
- `leastHerbrandModelRelEnv_complete` — derivable atoms appear in the env
- `leastHerbrandModelRelEnv_sound` — env tuples come from the least model

## References

- Tantow et al., *Certifying Datalog Reasoning in Lean 4*, ITP 2025
-/

namespace Mettapedia.Logic.LP

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Section 0: Injective encoding typeclass -/

/-- A typeclass asserting that `ToString` serialization is injective. -/
class InjectiveToString (α : Type*) [ToString α] : Prop where
  toString_injective : Function.Injective (toString : α → String)

instance : InjectiveToString String where
  toString_injective := fun _ _ h => h

/-! ## Section 1: Encoding ground atoms as OSLF Patterns -/

variable {σ : LPSignature} [hFF : IsEmpty σ.functionSymbols]

/-- Encode a constant as a zero-argument `Pattern.apply` node. -/
def constToPattern [ToString σ.constants] (c : σ.constants) : Pattern :=
  .apply (toString c) []

omit hFF in
/-- `constToPattern` is injective under `InjectiveToString`. -/
theorem constToPattern_injective [ToString σ.constants]
    [InjectiveToString σ.constants] : Function.Injective (@constToPattern σ _) := by
  intro c c' h
  simp only [constToPattern, Pattern.apply.injEq] at h
  exact InjectiveToString.toString_injective h.1

/-- The argument tuple of a ground atom encoded as OSLF `Pattern`s.
    Uses `List.ofFn` to convert `Fin n → GroundTerm σ` to a list,
    then `GroundTerm.toConst` for the function-free encoding. -/
def groundAtomArgs [ToString σ.constants] (a : GroundAtom σ) : List Pattern :=
  List.ofFn (fun i => constToPattern (a.args i).toConst)

/-- `groundAtomArgs` is injective (given same symbol) under `InjectiveToString`.

    If two ground atoms have the same symbol and the same encoded argument tuple,
    they are equal. -/
theorem groundAtomArgs_injective [ToString σ.constants]
    [InjectiveToString σ.constants]
    {a a' : GroundAtom σ} (hargs : groundAtomArgs a = groundAtomArgs a')
    (hsym : a.symbol = a'.symbol) : a = a' := by
  cases a with | mk sa aa =>
  cases a' with | mk sa' aa' =>
  simp only at hsym
  subst hsym
  congr
  funext i
  simp only [groundAtomArgs] at hargs
  have hfn := List.ofFn_injective hargs
  have hi : constToPattern ((aa i).toConst) = constToPattern ((aa' i).toConst) :=
    congr_fun hfn i
  have hci := constToPattern_injective hi
  calc aa i = GroundTerm.ofConst (aa i).toConst := (GroundTerm.ofConst_toConst _).symm
    _ = GroundTerm.ofConst (aa' i).toConst := congrArg _ hci
    _ = aa' i := GroundTerm.ofConst_toConst _

/-- The full encoding of a ground atom as a `Pattern.apply` node. -/
def groundAtomToPattern [ToString σ.relationSymbols] [ToString σ.constants]
    (a : GroundAtom σ) : Pattern :=
  .apply (toString a.symbol) (groundAtomArgs a)

/-! ## Section 2: Lifting a FinInterpretation to a RelationEnv -/

/-- Construct a `RelationEnv` from a finite LP interpretation. -/
noncomputable def lpToRelEnv [ToString σ.relationSymbols] [ToString σ.constants]
    (I : FinInterpretation σ) : RelationEnv where
  tuples rel _ :=
    I.toList.filterMap fun a =>
      if toString a.symbol = rel then some (groundAtomArgs a) else none

/-! ## Section 3: Correctness of the encoding -/

/-- Atoms in `I` appear as tuples in the `lpToRelEnv I` environment. -/
theorem mem_lpToRelEnv [ToString σ.relationSymbols] [ToString σ.constants]
    (I : FinInterpretation σ) (a : GroundAtom σ) (ha : a ∈ I) (qs : List Pattern) :
    groundAtomArgs a ∈ (lpToRelEnv I).tuples (toString a.symbol) qs := by
  simp only [lpToRelEnv]
  apply List.mem_filterMap.mpr
  exact ⟨a, Finset.mem_toList.mpr ha, by simp⟩

/-- Characterization: tuples in `lpToRelEnv I` correspond to atoms in `I`. -/
theorem lpToRelEnv_iff [ToString σ.relationSymbols] [ToString σ.constants]
    (I : FinInterpretation σ) (rel : String) (qs : List Pattern) (t : List Pattern) :
    t ∈ (lpToRelEnv I).tuples rel qs ↔
    ∃ a ∈ I, toString a.symbol = rel ∧ t = groundAtomArgs a := by
  simp only [lpToRelEnv, List.mem_filterMap, Finset.mem_toList]
  constructor
  · rintro ⟨a, ha, ht⟩
    split_ifs at ht with h
    exact ⟨a, ha, h, (Option.some.inj ht).symm⟩
  · rintro ⟨a, ha, hrel, ht⟩
    exact ⟨a, ha, by simp [hrel, ht]⟩

/-! ## Section 4: leastHerbrandModel as a RelationEnv -/

/-- The least Herbrand model as a `RelationEnv`. -/
noncomputable def leastHerbrandModelRelEnv
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    [ToString σ.relationSymbols] [ToString σ.constants]
    (kb : KnowledgeBase σ) : RelationEnv :=
  lpToRelEnv (leastHerbrandModelFin kb)

/-- EDB facts appear in the leastHerbrandModel relation environment. -/
theorem leastHerbrandModelRelEnv_db
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    [ToString σ.relationSymbols] [ToString σ.constants]
    (kb : KnowledgeBase σ) (a : GroundAtom σ) (ha : a ∈ kb.db) (qs : List Pattern) :
    groundAtomArgs a ∈ (leastHerbrandModelRelEnv kb).tuples (toString a.symbol) qs := by
  apply mem_lpToRelEnv
  rw [mem_leastHerbrandModelFin_iff]
  exact leastHerbrandModel_db kb a ha

/-! ## Section 5: End-to-end bridge soundness and completeness -/

/-- **Completeness**: every derivable atom appears in the relation environment. -/
theorem leastHerbrandModelRelEnv_complete
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    [ToString σ.relationSymbols] [ToString σ.constants]
    (kb : KnowledgeBase σ) (a : GroundAtom σ) (ha : a ∈ leastHerbrandModel kb)
    (qs : List Pattern) :
    groundAtomArgs a ∈ (leastHerbrandModelRelEnv kb).tuples (toString a.symbol) qs := by
  apply mem_lpToRelEnv
  rwa [mem_leastHerbrandModelFin_iff]

/-- **Soundness**: every tuple in the relation environment comes from the least model. -/
theorem leastHerbrandModelRelEnv_sound
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    [ToString σ.relationSymbols] [ToString σ.constants]
    (kb : KnowledgeBase σ) (rel : String) (qs : List Pattern) (t : List Pattern)
    (ht : t ∈ (leastHerbrandModelRelEnv kb).tuples rel qs) :
    ∃ a ∈ leastHerbrandModel kb, toString a.symbol = rel ∧ t = groundAtomArgs a := by
  rw [leastHerbrandModelRelEnv, lpToRelEnv_iff] at ht
  obtain ⟨a, ha, hrel, heq⟩ := ht
  exact ⟨a, (mem_leastHerbrandModelFin_iff kb a).mp ha, hrel, heq⟩

end Mettapedia.Logic.LP
