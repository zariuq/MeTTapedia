import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure
import Mettapedia.TypeTheory.UniverseLevel.Algebra
import Mettapedia.TypeTheory.UniverseLevel.ZFSetTower
import Mettapedia.TypeTheory.TarskiUniverseEmbedding

/-!
# Internal set universes interpreting the level algebra

The tower of closed universes over a level order is a strictly growing tower of actual
internal sets, starting from a supplied seed set. Codes are members of these sets, and
decoding takes their members. Cumulative lifts preserve the underlying set exactly.

Every level codes the code carrier of every earlier level (`universeCodeBelow`,
`embeddingOfLt`). At a successor level this is the code of its predecessor (`universeCode`,
`successorEmbedding`). At a level without a predecessor the universe codes all the earlier
ones, and it has codes that are lifted from no earlier level: the set of the earlier
universes is one (`earlierUniversesCode`, `earlierUniversesCode_not_lifted`). Its elements
are the levels below (`earlierLevelsEquiv`), so a family of codes indexed by the levels below
a level has a product code (`levelPiCode`, `decodeLevelPi`), at the maximum of the bound and
the level of the family. Indexed by the earlier universes, that product is a code at no level
below the bound when it has an element (`levelPiCode_notMem_of_lt`); with a smaller index code
for the same levels the product is at that index's level (`indexedPiCode`). Over a seed that
declares an index set for the natural numbers, countably many levels have such an index at
every level, so their product is a code at the level of the family (`countableLevelPiCode`);
over the empty seed the lowest stage has no such index set
(`finiteRankIndex_notMem_empty_seed`).

Dependent product and sum codes are the actual graphs and Kuratowski pairs
of `ZFSetDependentProducts`. Their decoding is an equivalence, not literal
equality with Lean Pi/Sigma types. Level expressions are interpreted
through their least-level/successor/maximum and substitution semantics.
This is universe and type-former model content, not a full native DTT model.

The level order is a parameter: the natural numbers and the ordinal notations below ε₀ are
instances.
-/

open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetDependentProducts
open Mettapedia.TypeTheory.TarskiUniverseCapabilities
open Mettapedia.TypeTheory.TarskiUniverseEmbedding
open Mettapedia.TypeTheory.UniverseClosureProfiles

universe u

variable {L : Type} [LevelOrder L]

/-! ## Successor stages -/

/-- Every stage is a member of the stage at the successor level. -/
theorem universeSet_mem_succ (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    universeSet h seed l ∈ universeSet h seed (LevelOrder.succ l) :=
  universeSet_mem_of_lt h seed (LevelOrder.lt_succ l)

/-- Every stage is a subset of the stage at the successor level. -/
theorem universeSet_subset_succ (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    universeSet h seed l ⊆ universeSet h seed (LevelOrder.succ l) :=
  universeSet_mono h seed (LevelOrder.le_succ l)

/-- Over the natural numbers, every stage is a member of the next one. -/
theorem universeSet_mem_next (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    universeSet h seed n ∈ universeSet h seed (n + 1) :=
  universeSet_mem_succ h seed n

/-- Over the natural numbers, every stage is a subset of the next one. -/
theorem universeSet_subset_next (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    universeSet h seed n ⊆ universeSet h seed (n + 1) :=
  universeSet_subset_succ h seed n

/-! ## Codes, decoding and cumulative lifts -/

abbrev Code (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) := Elements (universeSet h seed l)

abbrev El {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {l : L} (code : Code h seed l) := Elements code.1

/-- The codes of the tower over the level order `L`, as a family of universes of codes. -/
noncomputable def family (L : Type) [LevelOrder L] (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    TarskiCodeFamily.{0, u + 1, u + 1} where
  Level := L
  Code := Code h seed
  El _ := El

def liftCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (below : i ≤ j) (code : Code h seed i) : Code h seed j :=
  ⟨code.1, universeSet_mono h seed below code.2⟩

theorem liftCode_refl {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i : L} (code : Code h seed i) :
    liftCode (le_refl i) code = code := rfl

theorem liftCode_trans {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j k : L}
    (first : i ≤ j) (second : j ≤ k) (code : Code h seed i) :
    liftCode (le_trans first second) code = liftCode second (liftCode first code) := rfl

theorem decode_liftCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (below : i ≤ j) (code : Code h seed i) : El (liftCode below code) = El code := rfl

noncomputable def cumulative (L : Type) [LevelOrder L] (h : CofinalInaccessibles.{u})
    (seed : ZFSet.{u}) : (family L h seed).Cumulative (fun i j : L => i ≤ j) where
  lift := liftCode
  decodeLift _ code := Equiv.refl (El code)

/-! ## Every level codes the earlier ones -/

/-- The code, at a level, of the code carrier of an earlier level. -/
noncomputable def universeCodeBelow (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {c d : L}
    (below : c < d) : Code h seed d :=
  ⟨universeSet h seed c, universeSet_mem_of_lt h seed below⟩

theorem decode_universeCodeBelow (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {c d : L}
    (below : c < d) : El (universeCodeBelow h seed below) = Code h seed c := rfl

/-- Lifting the code of an earlier code carrier gives its code at the higher level. -/
theorem liftCode_universeCodeBelow (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {c d e : L}
    (below : c < d) (le : d ≤ e) :
    liftCode le (universeCodeBelow h seed below) =
      universeCodeBelow h seed (lt_of_lt_of_le below le) := rfl

/-- The code of a level's code carrier at the next level. -/
noncomputable def universeCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    Code h seed (LevelOrder.succ l) :=
  universeCodeBelow h seed (LevelOrder.lt_succ l)

theorem decode_universeCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    El (universeCode h seed l) = Code h seed l := rfl

/-- A level embeds every earlier level: it codes the earlier code carrier and each of the
earlier codes. -/
noncomputable def embeddingOfLt (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {c d : L}
    (below : c < d) :
    UniverseEmbedding (universeAt (family L h seed) d) (universeAt (family L h seed) c) where
  codeCarrier := universeCodeBelow h seed below
  decodeCodeCarrier := Equiv.refl _
  decodedType := liftCode (L := L) (le_of_lt below)
  decodeDecodedType _ := Equiv.refl _

noncomputable def successorEmbedding (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    UniverseEmbedding (universeAt (family L h seed) (LevelOrder.succ l : L))
      (universeAt (family L h seed) l) :=
  embeddingOfLt h seed (LevelOrder.lt_succ l)

/-- The code, at a level, of the set of the universes at the levels below it. -/
noncomputable def earlierUniversesCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    Code h seed l :=
  ⟨earlierStages h seed l, earlierStages_mem h seed l⟩

/-- **A level has codes that no earlier level has**: the set of the earlier universes is the
lift of no code of an earlier level. -/
theorem earlierUniversesCode_not_lifted (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    {c d : L} (below : c < d) (code : Code h seed c) :
    liftCode (le_of_lt below) code ≠ earlierUniversesCode h seed d := by
  intro same
  have value : code.1 = earlierStages h seed d := congrArg Subtype.val same
  exact earlierStages_notMem_of_lt h seed below (value ▸ code.2)

/-- The universe at an earlier level, as an element of the set of the earlier universes. -/
noncomputable def earlierUniverse (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {l : L}
    (c : {c : L // c < l}) : El (earlierUniversesCode h seed l) :=
  ⟨universeSet h seed c.1, mem_earlierStages.mpr ⟨c.1, c.2, rfl⟩⟩

theorem earlierUniverse_bijective (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    Function.Bijective
      (earlierUniverse h seed : {c : L // c < l} → El (earlierUniversesCode h seed l)) := by
  constructor
  · intro c d same
    exact Subtype.ext (universeSet_injective h seed (congrArg Subtype.val same))
  · rintro ⟨x, hx⟩
    obtain ⟨c, below, rfl⟩ := mem_earlierStages.mp hx
    exact ⟨⟨c, below⟩, rfl⟩

/-- **The elements of the set of earlier universes are the levels below.** -/
noncomputable def earlierLevelsEquiv (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    {c : L // c < l} ≃ El (earlierUniversesCode h seed l) :=
  Equiv.ofBijective _ (earlierUniverse_bijective h seed l)

theorem earlierLevelsEquiv_apply (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {l : L}
    (c : {c : L // c < l}) :
    (earlierLevelsEquiv h seed l c).1 = universeSet h seed c.1 := rfl

/-! ## Dependent products and sums at the maximum level -/

noncomputable def fibres {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (a : Code h seed i) (b : El a → Code h seed j) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ a.1 then (b ⟨x, hx⟩).1 else ∅

theorem fibres_at {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (a : Code h seed i) (b : El a → Code h seed j) (x : El a) :
    fibres a b x.1 = (b x).1 := by
  simp only [fibres, dif_pos x.2]

noncomputable def piCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (a : Code h seed i) (b : El a → Code h seed j) : Code h seed (max i j) :=
  ⟨piSet a.1 (fibres a b), (universeSet_closed h seed _).piSet_mem
    (universeSet_mono h seed (le_max_left i j) a.2) _ (fun x hx => by
      rw [fibres_at a b ⟨x, hx⟩]
      exact universeSet_mono h seed (le_max_right i j) (b ⟨x, hx⟩).2)⟩

noncomputable def sigmaCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (a : Code h seed i) (b : El a → Code h seed j) : Code h seed (max i j) :=
  ⟨sigmaSet a.1 (fibres a b), (universeSet_closed h seed _).sigmaSet_mem
    (universeSet_mono h seed (le_max_left i j) a.2) _ (fun x hx => by
      rw [fibres_at a b ⟨x, hx⟩]
      exact universeSet_mono h seed (le_max_right i j) (b ⟨x, hx⟩).2)⟩

noncomputable def decodePi {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (a : Code h seed i) (b : El a → Code h seed j) : El (piCode a b) ≃ ((x : El a) → El (b x)) :=
  (piEquiv a.1 (fibres a b)).trans (Equiv.piCongrRight
    (fun x => Equiv.cast (congrArg Elements (fibres_at a b x))))

noncomputable def decodeSigma {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : L}
    (a : Code h seed i) (b : El a → Code h seed j) : El (sigmaCode a b) ≃ (Σ x : El a, El (b x)) :=
  (sigmaEquiv a.1 (fibres a b)).trans (Equiv.sigmaCongrRight
    (fun x => Equiv.cast (congrArg Elements (fibres_at a b x))))

theorem piClosed (L : Type) [LevelOrder L] (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (family L h seed).PiClosed := by
  intro n a b
  let code : Code (L := L) h seed n := ⟨(piCode (L := L) a b).1, by
    have hc := (piCode (L := L) a b).2
    exact universeSet_mono (L := L) h seed (max_le (le_refl _) (le_refl _)) hc⟩
  exact ⟨code, ⟨decodePi (L := L) a b⟩⟩

theorem sigmaClosed (L : Type) [LevelOrder L] (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (family L h seed).SigmaClosed := by
  intro n a b
  let code : Code (L := L) h seed n := ⟨(sigmaCode (L := L) a b).1, by
    have hc := (sigmaCode (L := L) a b).2
    exact universeSet_mono (L := L) h seed (max_le (le_refl _) (le_refl _)) hc⟩
  exact ⟨code, ⟨decodeSigma (L := L) a b⟩⟩

/-- Cumulative lifts change only universe-membership proofs. They do not
re-encode the dependent function graphs. -/
theorem piCode_lift_underlying {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j i' j' : L}
    (hi : i ≤ i') (hj : j ≤ j') (a : Code h seed i) (b : El a → Code h seed j) :
    (piCode (liftCode hi a) (fun x => liftCode hj (b x))).1 = (piCode a b).1 := rfl

theorem sigmaCode_lift_underlying {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j i' j' : L}
    (hi : i ≤ i') (hj : j ≤ j') (a : Code h seed i) (b : El a → Code h seed j) :
    (sigmaCode (liftCode hi a) (fun x => liftCode hj (b x))).1 = (sigmaCode a b).1 := rfl

/-- Semantic context substitution is pullback. No environment-dependent
re-encoding is inserted by either dependent type former. -/
theorem piCode_context_substitution {h : CofinalInaccessibles.{u}}
    {seed : ZFSet.{u}} {i j : L} {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → Code h seed i) (b : (γ : Γ) → El (a γ) → Code h seed j) :
    (fun γ => piCode (a γ) (b γ)) ∘ θ =
      (fun δ => piCode (a (θ δ)) (b (θ δ))) := rfl

theorem sigmaCode_context_substitution {h : CofinalInaccessibles.{u}}
    {seed : ZFSet.{u}} {i j : L} {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → Code h seed i) (b : (γ : Γ) → El (a γ) → Code h seed j) :
    (fun γ => sigmaCode (a γ) (b γ)) ∘ θ =
      (fun δ => sigmaCode (a (θ δ)) (b (θ δ))) := rfl

/-! ## Products indexed by the levels below a level -/

/-- The product of a family of codes over an index type whose members are the elements of a
code. The product is a code at the maximum of the level of the index and the level of the
family. -/
noncomputable def indexedPiCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i d : L}
    {ι : Type} (index : Code h seed i) (indexing : ι ≃ El index) (F : ι → Code h seed d) :
    Code h seed (max i d) :=
  piCode index (fun x => F (indexing.symm x))

/-- Its elements are the families with one element at each index. -/
noncomputable def decodeIndexedPi {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i d : L}
    {ι : Type} (index : Code h seed i) (indexing : ι ≃ El index) (F : ι → Code h seed d) :
    El (indexedPiCode index indexing F) ≃ ((c : ι) → El (F c)) :=
  (decodePi _ _).trans (Equiv.piCongrLeft' (fun c => El (F c)) indexing).symm

/-- **The product of a family of codes indexed by the levels below a level.** The index is
the code of the set of earlier universes, so the product has a code at the maximum of the
bound and the level of the family. With another index code for the levels below the bound,
`indexedPiCode` gives the product at the level of that index instead. -/
noncomputable def levelPiCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {l d : L}
    (F : {c : L // c < l} → Code h seed d) : Code h seed (max l d) :=
  indexedPiCode (earlierUniversesCode h seed l) (earlierLevelsEquiv h seed l) F

/-- **Its elements are the families with one element at each level below.** -/
noncomputable def decodeLevelPi {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {l d : L}
    (F : {c : L // c < l} → Code h seed d) :
    El (levelPiCode F) ≃ ((c : {c : L // c < l}) → El (F c)) :=
  decodeIndexedPi _ _ F

/-- Lifting the family changes only universe-membership proofs, not the product set. -/
theorem levelPiCode_lift_underlying {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {l d d' : L}
    (below : d ≤ d') (F : {c : L // c < l} → Code h seed d) :
    (levelPiCode (fun c => liftCode below (F c))).1 = (levelPiCode F).1 := rfl

/-- **The product over the levels below `l`, indexed by the earlier universes, is a code at
no level below `l` when it has an element**: each of its functions has the set of the earlier
universes as its domain. -/
theorem levelPiCode_notMem_of_lt {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {l d c : L}
    (below : c < l) (F : {c : L // c < l} → Code h seed d)
    (inhabited : Nonempty (El (levelPiCode F))) :
    (levelPiCode F).1 ∉ universeSet h seed c := by
  intro member
  obtain ⟨⟨g, hg⟩⟩ := inhabited
  have closed := universeSet_closed h seed c
  have gMem : g ∈ universeSet h seed c := closed.transitive _ member hg
  have func := (mem_piSet.mp (show g ∈ piSet (earlierStages h seed l) _ from hg)).1
  have domain : earlierStages h seed l ⊆ ZFSet.sUnion (ZFSet.sUnion g) := by
    intro x hx
    obtain ⟨w, hw, -⟩ := func.2 x hx
    refine ZFSet.mem_sUnion.mpr ⟨{x}, ZFSet.mem_sUnion.mpr ⟨ZFSet.pair x w, hw, ?_⟩,
      ZFSet.mem_singleton.mpr rfl⟩
    exact ZFSet.mem_pair.mpr (Or.inl rfl)
  exact earlierStages_notMem_of_lt h seed below
    (closed.subset_mem (closed.union_mem (closed.union_mem gMem)) domain)

/-! ### The product of the finite universes

Over the ordinal notations below ε₀, the universes at the finite levels form a family indexed
by the levels below `ω`. Its product is a code at the level `ω`; it has an element, and it is
a code at no finite level. -/

/-- The product of the universes at all the finite levels. -/
noncomputable def finiteUniversesProduct (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    Code h seed (max Level.omega Level.omega) :=
  levelPiCode fun c : {c : Level // c < Level.omega} => universeCodeBelow h seed c.2

/-- It has an element: the family with the empty set at every finite level. -/
theorem finiteUniversesProduct_inhabited (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    Nonempty (El (finiteUniversesProduct h seed)) :=
  ⟨(decodeLevelPi _).symm fun c =>
    ⟨∅, (universeSet_closed h seed c.1).empty_mem (seed_mem_universeSet h seed c.1)⟩⟩

/-- It is a code at no finite level. -/
theorem finiteUniversesProduct_notMem_ofNat (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (k : Nat) : (finiteUniversesProduct h seed).1 ∉ universeSet h seed (Level.ofNat k) :=
  levelPiCode_notMem_of_lt (Level.ofNat_lt_omega k) _ (finiteUniversesProduct_inhabited h seed)

/-! ### A small index for countably many levels

A product over the levels below a bound is at the level of whatever code indexes those levels.
A seed that declares an index set for the natural numbers puts that set in every stage, so
countably many levels are indexed by a set of every universe, and their product is a code at
the level of the family itself. With the empty seed the lowest stage has no such index set. -/

open ZFSetIndexedClosure (finiteRank finiteRank_injective finiteRankIndex)

/-- The index set of the natural numbers is a member of every stage over a seed that declares
it. -/
theorem indices_mem_level (h : CofinalInaccessibles.{u}) (parameter : ZFSet.{u}) (l : L) :
    finiteRankIndex ∈ universeSet h (ZFSetIndexedClosure.seed parameter) l :=
  universeSet_mono h _ (LevelOrder.bot_le l) (by
    rw [universeSet_bot]
    exact ZFSetIndexedClosure.seed_contains_indices h parameter)

/-- **The seed matters**: over the empty seed, the index set of the natural numbers is not a
member of the lowest stage. -/
theorem finiteRankIndex_notMem_empty_seed (h : CofinalInaccessibles.{u}) :
    finiteRankIndex.{u} ∉ universeSet h ∅ (LevelOrder.bot : L) := by
  intro member
  rw [universeSet_bot] at member
  exact ZFSetIndexedClosure.finiteRankIndex_not_mem_finite_universe
    (univOf_minimal h
      (ZFSetIndexedClosure.finite_universe_closed.empty_mem
        (ZFSetIndexedClosure.finiteRank_mem_finite_universe 0))
      ZFSetIndexedClosure.finite_universe_closed member)

/-- An injection of a countable type into the natural numbers. -/
noncomputable def countableIndexMap (ι : Type) [Countable ι] : ι → Nat :=
  Classical.choose (exists_injective_nat ι)

theorem countableIndexMap_injective (ι : Type) [Countable ι] :
    Function.Injective (countableIndexMap ι) :=
  Classical.choose_spec (exists_injective_nat ι)

/-- The index set of a countable type: the finite ranks at the images of its members. -/
noncomputable def countableIndexSet (ι : Type) [Countable ι] : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ c : ι, finiteRank (countableIndexMap ι c) = x) finiteRankIndex

/-- The index set of a countable type is a code at every level, over a seed that declares the
index set of the natural numbers. -/
noncomputable def countableIndexCode (h : CofinalInaccessibles.{u}) (parameter : ZFSet.{u})
    (ι : Type) [Countable ι] (l : L) : Code h (ZFSetIndexedClosure.seed parameter) l :=
  ⟨countableIndexSet ι,
    (universeSet_closed h _ l).separation_mem (indices_mem_level h parameter l) _⟩

/-- Its elements are the members of the type. -/
noncomputable def countableIndexEquiv (h : CofinalInaccessibles.{u}) (parameter : ZFSet.{u})
    (ι : Type) [Countable ι] (l : L) : ι ≃ El (countableIndexCode h parameter ι l) :=
  Equiv.ofBijective
    (fun c => ⟨finiteRank (countableIndexMap ι c), by
      show finiteRank.{u} (countableIndexMap ι c) ∈ ZFSet.sep
        (fun x => ∃ c : ι, finiteRank.{u} (countableIndexMap ι c) = x) finiteRankIndex
      exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_range_self (f := finiteRank.{u}) _, c, rfl⟩⟩)
    ⟨fun _ _ same =>
        countableIndexMap_injective ι (finiteRank_injective (congrArg Subtype.val same)),
      fun ⟨x, hx⟩ => by
        have member : x ∈ ZFSet.sep
            (fun x => ∃ c : ι, finiteRank.{u} (countableIndexMap ι c) = x) finiteRankIndex := hx
        obtain ⟨-, c, rfl⟩ := ZFSet.mem_sep.mp member
        exact ⟨c, rfl⟩⟩

/-- **With a declared index for the natural numbers, a product over countably many levels is a
code at the level of its family.** -/
noncomputable def countableLevelPiCode {h : CofinalInaccessibles.{u}} {parameter : ZFSet.{u}}
    {l d : L} [Countable {c : L // c < l}]
    (F : {c : L // c < l} → Code h (ZFSetIndexedClosure.seed parameter) d) :
    Code h (ZFSetIndexedClosure.seed parameter) d :=
  liftCode (max_le (le_refl d) (le_refl d))
    (indexedPiCode (countableIndexCode h parameter {c : L // c < l} d)
      (countableIndexEquiv h parameter {c : L // c < l} d) F)

/-- Its elements are the families with one element at each level below. -/
noncomputable def decodeCountableLevelPi {h : CofinalInaccessibles.{u}} {parameter : ZFSet.{u}}
    {l d : L} [Countable {c : L // c < l}]
    (F : {c : L // c < l} → Code h (ZFSetIndexedClosure.seed parameter) d) :
    El (countableLevelPiCode F) ≃ ((c : {c : L // c < l}) → El (F c)) :=
  (decodeIndexedPi (countableIndexCode h parameter {c : L // c < l} d)
    (countableIndexEquiv h parameter {c : L // c < l} d) F :
      El (indexedPiCode (countableIndexCode h parameter {c : L // c < l} d)
        (countableIndexEquiv h parameter {c : L // c < l} d) F) ≃ _)

/-- **The two products have the same elements**: the product indexed by the earlier universes,
at the maximum of the bound and the family's level, and the product indexed by the small index,
at the family's level, are in bijection. They are different sets, at different levels. -/
noncomputable def levelPiEquivCountable {h : CofinalInaccessibles.{u}} {parameter : ZFSet.{u}}
    {l d : L} [Countable {c : L // c < l}]
    (F : {c : L // c < l} → Code h (ZFSetIndexedClosure.seed parameter) d) :
    El (levelPiCode F) ≃ El (countableLevelPiCode F) :=
  (decodeLevelPi F).trans (decodeCountableLevelPi F).symm

/-- Over the ordinal notations, with a declared index: the sequences of finite ranks indexed by
the finite levels are a code of the lowest universe. -/
noncomputable def finiteLevelSequences (h : CofinalInaccessibles.{u}) (parameter : ZFSet.{u}) :
    Code h (ZFSetIndexedClosure.seed parameter) (LevelOrder.bot : Level) :=
  countableLevelPiCode (l := Level.omega) fun _ =>
    ⟨finiteRankIndex, indices_mem_level h parameter LevelOrder.bot⟩

/-- It has an element: the constant sequence. -/
theorem finiteLevelSequences_inhabited (h : CofinalInaccessibles.{u}) (parameter : ZFSet.{u}) :
    Nonempty (El (finiteLevelSequences h parameter)) :=
  ⟨(decodeCountableLevelPi (l := Level.omega)
      (fun _ => (⟨finiteRankIndex, indices_mem_level h parameter LevelOrder.bot⟩ :
        Code h (ZFSetIndexedClosure.seed parameter) (LevelOrder.bot : Level)))).symm
    fun _ => ⟨finiteRank 0, ZFSet.mem_range_self (f := finiteRank.{u}) 0⟩⟩

/-! ## The level algebra -/

noncomputable def interpretLevel (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (level : LevelExpr L) : ZFSet.{u} :=
  universeSet h seed (level.eval valuation)

theorem interpretLevel_zero (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (valuation : Nat → L) :
    interpretLevel h seed valuation (.const LevelOrder.bot) = univOf h seed := universeSet_bot h seed

theorem interpretLevel_successor (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (level : LevelExpr L) :
    interpretLevel h seed valuation level ∈ interpretLevel h seed valuation (.succ level) :=
  universeSet_mem_succ h seed _

theorem interpretLevel_max_left (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (left right : LevelExpr L) :
    interpretLevel h seed valuation left ⊆ interpretLevel h seed valuation (.max left right) :=
  universeSet_mono h seed (le_max_left _ _)

theorem interpretLevel_max_right (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (left right : LevelExpr L) :
    interpretLevel h seed valuation right ⊆ interpretLevel h seed valuation (.max left right) :=
  universeSet_mono h seed (le_max_right _ _)

/-- Comparisons of level expressions are inclusions of their universes, and conversely. -/
theorem interpretLevel_subset_iff (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (left right : LevelExpr L) :
    interpretLevel h seed valuation left ⊆ interpretLevel h seed valuation right ↔
      left.eval valuation ≤ right.eval valuation :=
  universeSet_subset_iff h seed

/-- Strict comparisons of level expressions are memberships of their universes, and
conversely. -/
theorem interpretLevel_mem_iff (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (left right : LevelExpr L) :
    interpretLevel h seed valuation left ∈ interpretLevel h seed valuation right ↔
      left.eval valuation < right.eval valuation :=
  universeSet_mem_iff h seed

/-- Level expressions with the same universe have the same value. -/
theorem interpretLevel_eq_iff (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (left right : LevelExpr L) :
    interpretLevel h seed valuation left = interpretLevel h seed valuation right ↔
      left.eval valuation = right.eval valuation :=
  (universeSet_injective h seed).eq_iff

theorem interpretLevel_substitution (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (θ : Nat → LevelExpr L) (level : LevelExpr L) :
    interpretLevel h seed valuation (level.subst θ) =
      interpretLevel h seed (fun n => (θ n).eval valuation) level := by
  unfold interpretLevel
  rw [LevelExpr.eval_subst]

theorem interpretedCode_substitution (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → L) (θ : Nat → LevelExpr L) (level : LevelExpr L) :
    Code h seed ((level.subst θ).eval valuation) =
      Code h seed (level.eval (fun n => (θ n).eval valuation)) := by
  rw [LevelExpr.eval_subst]

theorem universeSet_no_self_membership (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    universeSet h seed l ∉ universeSet h seed l := ZFSet.mem_irrefl _

theorem successor_not_equal (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (l : L) :
    universeSet h seed (LevelOrder.succ l) ≠ universeSet h seed l :=
  (universeSet_ne_of_lt h seed (LevelOrder.lt_succ l)).symm

/-! ## A nonconstant family already present over the empty seed

This control concerns finite set codes only; it does not claim that any
specific native inductive datatype has been interpreted.
-/

namespace Controls

noncomputable def emptyCode (h : CofinalInaccessibles.{u}) : Code h ∅ 0 :=
  ⟨∅, seed_mem_universeSet h ∅ 0⟩

noncomputable def twoCode (h : CofinalInaccessibles.{u}) : Code h ∅ 0 :=
  ⟨ZFSetDependentProducts.Controls.two,
    (universeSet_closed h ∅ 0).power_mem
      ((universeSet_closed h ∅ 0).power_mem (emptyCode h).2)⟩

noncomputable def varyingCodes (h : CofinalInaccessibles.{u})
    (x : El (twoCode h)) : Code h ∅ 0 := by
  classical
  refine ⟨ZFSetDependentProducts.Controls.varying x.1, ?_⟩
  unfold ZFSetDependentProducts.Controls.varying
  split
  · exact (universeSet_closed h ∅ 0).singleton_mem (emptyCode h).2
  · exact (twoCode h).2

theorem varying_pi_underlying (h : CofinalInaccessibles.{u}) :
    (piCode (twoCode h) (varyingCodes h)).1 =
      piSet ZFSetDependentProducts.Controls.two ZFSetDependentProducts.Controls.varying := by
  change piSet ZFSetDependentProducts.Controls.two (fibres (twoCode h) (varyingCodes h)) = _
  apply piSet_congr
  intro x hx
  exact fibres_at (twoCode h) (varyingCodes h) ⟨x, hx⟩

theorem varying_pi_inhabited (h : CofinalInaccessibles.{u}) :
    Nonempty (El (piCode (twoCode h) (varyingCodes h))) := by
  let witness := ZFSetDependentProducts.Controls.varyingFunction.{u}
  refine ⟨⟨witness.1, ?_⟩⟩
  rw [varying_pi_underlying]
  exact witness.2

theorem varying_fibres_not_equal (h : CofinalInaccessibles.{u}) :
    (varyingCodes h ⟨∅, ZFSetDependentProducts.Controls.empty_mem_two⟩).1 ≠
      (varyingCodes h ⟨ZFSet.powerset ∅,
        ZFSetDependentProducts.Controls.power_empty_mem_two⟩).1 :=
  ZFSetDependentProducts.Controls.varying_fibres_distinct

theorem empty_code_not_inhabited (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (El (emptyCode h)) := by
  rintro ⟨⟨x, impossible⟩⟩
  exact ZFSet.notMem_empty x impossible

end Controls

#print axioms universeSet_closed
#print axioms universeCodeBelow
#print axioms earlierUniversesCode_not_lifted
#print axioms earlierLevelsEquiv
#print axioms levelPiCode
#print axioms decodeLevelPi
#print axioms levelPiCode_notMem_of_lt
#print axioms finiteUniversesProduct_notMem_ofNat
#print axioms countableLevelPiCode
#print axioms finiteRankIndex_notMem_empty_seed
#print axioms finiteLevelSequences_inhabited
#print axioms interpretLevel_subset_iff
#print axioms universeSet_seed_mono
#print axioms universeSet_mono
#print axioms cumulative
#print axioms successorEmbedding
#print axioms piCode
#print axioms sigmaCode
#print axioms decodePi
#print axioms decodeSigma
#print axioms piClosed
#print axioms sigmaClosed
#print axioms piCode_lift_underlying
#print axioms piCode_context_substitution
#print axioms interpretLevel_substitution
#print axioms successor_not_equal
#print axioms Controls.varying_pi_inhabited
#print axioms Controls.varying_fibres_not_equal
#print axioms Controls.empty_code_not_inhabited

end Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
