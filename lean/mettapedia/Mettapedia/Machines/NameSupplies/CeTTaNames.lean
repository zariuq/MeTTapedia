import Mettapedia.Machines.NameSupplies.HashCollision
import Mettapedia.Machines.NameSupplies.PortableNames
import Mettapedia.Machines.PartialHashIndex

/-!
# CeTTa's generated-name representation

The counted form in `name_supply.h` compares its block token and two words.
Printing a deep counted name uses the block's digest instead of its token.
The form called unforgeable keeps only the digest. The model distinguishes
these equality contracts and the random-function premise of the collision
bound.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies.CeTTaNames

abbrev Word := BitVec 64
abbrev Digest := Fin (2 ^ 128)

/-- The block token is abstract identity during its live lifetime. -/
structure Counted where
  block : Option ℕ
  path : Word
  counter : Word
  deriving DecidableEq

/-- The coordinates read by the printer after the path code has been
decoded. The form tag and name kind are supplied by its caller. -/
def spelling (blockKey : ℕ → Digest) (name : Counted) : Option Digest × Word × Word :=
  (name.block.map blockKey, name.path, name.counter)

def root (counter : Word) : Counted := ⟨none, 1, counter⟩

theorem root_spelling_exact (key : ℕ → Digest) (first second : Word) :
    spelling key (root first) = spelling key (root second) ↔ first = second := by
  simp [spelling, root]

theorem deep_equality_survives_collision (key : ℕ → Digest) {left right : ℕ}
    (distinct : left ≠ right) (same : key left = key right) (path count : Word) :
    let first : Counted := ⟨some left, path, count⟩
    let second : Counted := ⟨some right, path, count⟩
    first ≠ second ∧ spelling key first = spelling key second := by
  dsimp only
  refine ⟨?_, by simp [spelling, same]⟩
  intro equal
  exact distinct (Option.some.inj (congrArg Counted.block equal))

/-- An exact lookup can use the digest as an index while retaining the
block token locally. A digest-only spelling can collide. -/
theorem indexed_lookup_exact (tag : Counted → ℕ) (keys : List Counted) (query : Counted) :
    Mettapedia.Machines.PartialHashIndex.bucketContains (fun x y => decide (x = y))
      (fun key => some (tag key)) keys query (tag query) =
    Mettapedia.Machines.PartialHashIndex.contains (fun x y => decide (x = y)) keys query := by
  apply Mettapedia.Machines.PartialHashIndex.bucket_refines
  · intro left right first second equal firstCode secondCode
    have same := of_decide_eq_true equal
    subst right
    exact Option.some.inj (firstCode.symm.trans secondCode)
  · exact fun key _ => ⟨tag key, rfl⟩
  · rfl

/-- One digest update per occupied block. A stored key is enough to keep
folding future word paths, independently of the number already folded. -/
def blockDigest (keyed : Digest → Word → Digest) (start : Digest) (blocks : List Word) : Digest :=
  blocks.foldl keyed start

theorem blockDigest_incremental (keyed : Digest → Word → Digest) (start : Digest)
    (prefixBlocks suffixBlocks : List Word) :
    blockDigest keyed start (prefixBlocks ++ suffixBlocks) =
      blockDigest keyed (blockDigest keyed start prefixBlocks) suffixBlocks :=
  List.foldl_append

/-- The digest-only mode identifies two inputs with the same returned
digest. For distinct uniform queries this is its collision bound. -/
theorem digest_only_risk (requests : ℕ) :
    ((HashCollision.collisions requests (2 ^ 128)).card : ℚ) / ((2 ^ 128 : ℕ) ^ requests : ℕ) ≤
      (requests.choose 2 : ℚ) / (2 ^ 128 : ℕ) :=
  HashCollision.birthday_bound requests 128

theorem digest_only_capacity (requests : ℕ) (large : 2 ^ 128 < requests)
    (hash : Fin requests → Digest) :
    ∃ first second, first ≠ second ∧ hash first = hash second :=
  Fintype.exists_ne_map_eq_of_card_lt hash (by simpa using large)

#print axioms root_spelling_exact
#print axioms deep_equality_survives_collision
#print axioms indexed_lookup_exact
#print axioms blockDigest_incremental
#print axioms digest_only_risk
#print axioms digest_only_capacity

section Export

open Mettapedia.Algorithms.Collections.StableKeyEncoding (extend mem_extend_self extend_idxOf)
open Mettapedia.Machines.NameSupplies.PortableNames (Name serialize deserialize
  deserialize_serialize serialize_injective)

/-- Assign a stable portable key on escape, retaining the exact local
identity in the originating process. The append-only registry supplies a
serial that can outlive the block digest's usefulness. -/
def escape (issuer : ℕ) (registry : List Counted) (localName : Counted) :
    List Counted × List ℕ :=
  (extend registry localName, serialize ⟨issuer, (.all, registry.idxOf localName)⟩)

/-- A returning key resolves in its issuer incarnation. Other issuers use
their own handles for this portable key. -/
def returnToIssuer (issuer : ℕ) (registry : List Counted) (tokens : List ℕ) : Option Counted := do
  let name ← deserialize tokens
  if name.issuer = issuer ∧ name.stamp.1 = .all then registry[name.stamp.2]? else none

theorem escape_roundtrip (issuer : ℕ) (registry : List Counted) (localName : Counted) :
    returnToIssuer issuer (escape issuer registry localName).1
      (escape issuer registry localName).2 = some localName := by
  have lookup := List.getElem?_idxOf (mem_extend_self registry localName)
  rw [extend_idxOf] at lookup
  simp [escape, returnToIssuer, deserialize_serialize, lookup]

theorem distinct_escapes_after_collision (issuer : ℕ) (registry : List Counted)
    {left right : Counted} (distinct : left ≠ right) :
    (escape issuer registry left).2 ≠
      (escape issuer (escape issuer registry left).1 right).2 := by
  intro same
  have serial := congrArg (fun name : Name => name.stamp.2) (serialize_injective same)
  have previous : (extend registry left).idxOf left = (extend registry left).idxOf right :=
    (extend_idxOf registry left).trans serial
  exact distinct ((List.idxOf_inj (mem_extend_self registry left)).mp previous)

end Export

#print axioms escape_roundtrip
#print axioms distinct_escapes_after_collision

end Mettapedia.Machines.NameSupplies.CeTTaNames
