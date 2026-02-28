import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# PathMap Algebraic Structures

Lean 4 formalization of PathMap's algebraic interface (`ring.rs`).

PathMap is a trie-based data structure from the Hyperon MeTTa-Compiler project.
It supports four algebraic operations on trie-sets:

| Operation   | Set semantics                     | Rust trait            |
|-------------|-----------------------------------|-----------------------|
| `pjoin`     | union (paths in either operand)   | `Lattice::pjoin`      |
| `pmeet`     | intersection (paths in both)      | `Lattice::pmeet`      |
| `psubtract` | difference (in lhs but not rhs)   | `DistributiveLattice` |
| `prestrict` | prefix-filter (prefix in rhs)     | `Quantale`            |

Operations return `AlgebraicResult V` instead of `V` to avoid allocating when
the result is identical to one of the inputs (structural-sharing optimization).

## References
- `ring.rs`: `/home/zar/claude/hyperon/PathMap/src/ring.rs`
- PathMap book: `1.01.00_algebraic_ops.md`, `1.01.01_algebraic_traits.md`
-/

namespace Mettapedia.PathMap

/-! ## AlgebraicResult -/

/-- Result of a binary partial-lattice operation.

- `none`         : both inputs annihilate (both were "empty/bottom"); the output
                   should be discarded entirely.
- `identity`     : output is identical to one or both inputs (no new allocation
                   needed).  `isSelf` means the output equals the left (self)
                   argument; `isOther` means it equals the right (other).
                   Both may be true simultaneously (when inputs are equal and
                   either would serve as the identity).
- `element v`    : a genuinely new output value `v`.

This mirrors the Rust `AlgebraicResult<V>` enum in `ring.rs`, replacing the
bitmask with two explicit booleans for binary operations. -/
inductive AlgebraicResult (V : Type*) where
  /-- Both inputs annihilate; the output should be discarded (bottom) -/
  | none : AlgebraicResult V
  /-- Output is identical to one or both inputs.
      `isSelf` = result equals the left (self) argument.
      `isOther` = result equals the right (other) argument.
      At least one of the two should be `true`. -/
  | identity (isSelf : Bool) (isOther : Bool) : AlgebraicResult V
  /-- A genuinely new output value -/
  | element : V → AlgebraicResult V
  deriving Repr, DecidableEq

namespace AlgebraicResult

variable {V W : Type*}

def isNone   : AlgebraicResult V → Bool | .none => true | _ => false
def isIdent  : AlgebraicResult V → Bool | .identity .. => true | _ => false
def isElem   : AlgebraicResult V → Bool | .element _ => true | _ => false

/-- Map the `element` payload, leaving `none` and `identity` unchanged. -/
def map (f : V → W) : AlgebraicResult V → AlgebraicResult W
  | .none => .none
  | .identity s o => .identity s o
  | .element v => .element (f v)

/-- Resolve to a concrete value given the original binary operands `a` and `b`. -/
def resolve (a b : V) : AlgebraicResult V → Option V
  | .none => .none                   -- Option.none (not AlgebraicResult.none)
  | .identity true _    => some a
  | .identity false true => some b
  | .identity false false => .none   -- malformed; safe fallback
  | .element v => some v

/-- Swap identity bits (used for commutativity arguments). -/
def swapIdent : AlgebraicResult V → AlgebraicResult V
  | .none => .none
  | .identity s o => .identity o s
  | .element v => .element v

@[simp] theorem swapIdent_none   : (none : AlgebraicResult V).swapIdent = .none := rfl
@[simp] theorem swapIdent_ident  (s o : Bool) :
    (identity s o : AlgebraicResult V).swapIdent = .identity o s := rfl
@[simp] theorem swapIdent_elem   (v : V) :
    (element v : AlgebraicResult V).swapIdent = .element v := rfl
@[simp] theorem swapIdent_swapIdent (r : AlgebraicResult V) :
    r.swapIdent.swapIdent = r := by cases r <;> simp [swapIdent]

/-- An `AlgebraicResult` is well-formed w.r.t. operands `a` and `b` when the
    identity flags are internally consistent: at least one flag must be `true`.

    The malformed case is `.identity false false`, which asserts neither input
    is the result — a contradiction for an identity result.  Well-formed results
    are exactly those for which `resolve` returns `some _` rather than `none`
    through the false-false fallback. -/
def WellFormed {V : Type*} (_ _ : V) : AlgebraicResult V → Prop
  | .none         => True
  | .identity s o => s ∨ o
  | .element _    => True

end AlgebraicResult

/-! ## PathMapLattice Typeclass -/

/-- A partial lattice: join (union) and meet (intersection) operations that
    return `AlgebraicResult` to support structural sharing. -/
class PathMapLattice (α : Type*) where
  /-- Union: a path appears in the result iff it appears in either operand. -/
  pjoin : α → α → AlgebraicResult α
  /-- Intersection: a path appears in the result iff it appears in both operands. -/
  pmeet : α → α → AlgebraicResult α

/-- A partial distributive lattice: extends `PathMapLattice` with subtraction.
    `psubtract a b` = set-difference: paths in `a` that are absent from `b`. -/
class PathMapDistributiveLattice (α : Type*) extends PathMapLattice α where
  /-- Set-difference (left-biased non-commutative). -/
  psubtract : α → α → AlgebraicResult α

/-- PathMap quantale: extends `PathMapDistributiveLattice` with restrict.
    `prestrict a b` = keep only those paths of `a` whose prefix appears in `b`. -/
class PathMapQuantale (α : Type*) extends PathMapDistributiveLattice α where
  /-- Prefix-filter: keep paths from `a` whose prefix appears in `b`. -/
  prestrict : α → α → AlgebraicResult α

/-! ## Algebraic Laws (value-level Prop typeclasses)

Laws are stated at the *resolved value* level using `AlgebraicResult.resolve`.
This correctly handles the case `a = b` (where ring.rs may set either identity
bit, not necessarily both) and the `None` case (empty/bottom inputs). -/

/-- Join is commutative at the resolved-value level:
    `pjoin a b` and `pjoin b a` resolve to the same value. -/
class JoinComm (α : Type*) [PathMapLattice α] : Prop where
  pjoin_comm : ∀ a b : α,
    (PathMapLattice.pjoin a b).resolve a b = (PathMapLattice.pjoin b a).resolve b a

/-- Join is idempotent: `pjoin a a` never produces a genuinely new element value.
    The result is always `None` or an `Identity` (no allocation needed). -/
class JoinIdem (α : Type*) [PathMapLattice α] : Prop where
  pjoin_idem : ∀ a : α, ¬(PathMapLattice.pjoin a a).isElem

/-- Meet is commutative at the resolved-value level. -/
class MeetComm (α : Type*) [PathMapLattice α] : Prop where
  pmeet_comm : ∀ a b : α,
    (PathMapLattice.pmeet a b).resolve a b = (PathMapLattice.pmeet b a).resolve b a

/-- Meet is idempotent: `pmeet a a` never produces a genuinely new element value. -/
class MeetIdem (α : Type*) [PathMapLattice α] : Prop where
  pmeet_idem : ∀ a : α, ¬(PathMapLattice.pmeet a a).isElem

/-- Absorption: join absorbs meet.
    If `pmeet a b` resolves to some `m`, then `pjoin a m` resolves back to `a`. -/
class Absorption (α : Type*) [PathMapLattice α] : Prop where
  join_absorbs_meet : ∀ a b m : α,
    (PathMapLattice.pmeet a b).resolve a b = some m →
    (PathMapLattice.pjoin a m).resolve a m = some a

/-! ## Concrete Instance: `Bool` (following ring.rs exactly) -/

/-- Boolean partial lattice, mirroring `ring.rs` Bool implementation.
    Boolean values represent "exists" (true) vs "absent/bottom" (false).
    `pjoin` = logical or; `pmeet` = logical and.
    Neither operation returns `none` because Bool forms a complete (not partial) lattice:
    false is the bottom, not "empty". -/
instance : PathMapLattice Bool where
  pjoin a b :=
    -- ring.rs: if !*self && *other { Identity(COUNTER_IDENT) } else { Identity(SELF_IDENT) }
    if !a && b then .identity false true   -- result = b (true wins)
    else .identity true false              -- result = a
  pmeet a b :=
    -- ring.rs: if *self && !*other { Identity(COUNTER_IDENT) } else { Identity(SELF_IDENT) }
    if a && !b then .identity false true   -- result = b (false wins)
    else .identity true false              -- result = a

instance : JoinComm Bool where
  pjoin_comm a b := by
    simp only [PathMapLattice.pjoin, AlgebraicResult.resolve]
    cases a <;> cases b <;> decide

instance : MeetComm Bool where
  pmeet_comm a b := by
    simp only [PathMapLattice.pmeet, AlgebraicResult.resolve]
    cases a <;> cases b <;> decide

instance : JoinIdem Bool where
  pjoin_idem a := by
    simp only [PathMapLattice.pjoin, AlgebraicResult.isElem]
    cases a <;> decide

instance : MeetIdem Bool where
  pmeet_idem a := by
    simp only [PathMapLattice.pmeet, AlgebraicResult.isElem]
    cases a <;> decide

instance : Absorption Bool where
  join_absorbs_meet a b m hm := by
    simp only [PathMapLattice.pmeet, AlgebraicResult.resolve] at hm
    cases a <;> cases b <;> simp_all [PathMapLattice.pjoin, AlgebraicResult.resolve]

/-! ## Concrete Instance: `Finset α` -/

/-- The PathMap distributive lattice on finite sets: union, intersection, difference.
    Laws for Finset follow straightforwardly from set theory. -/
instance {α : Type*} [DecidableEq α] : PathMapDistributiveLattice (Finset α) where
  pjoin a b :=
    if a = b then .identity true true
    else if a ⊆ b then .identity false true
    else if b ⊆ a then .identity true false
    else .element (a ∪ b)
  pmeet a b :=
    if (a ∩ b).card = 0 then .none
    else if a = b then .identity true true
    else if a ⊆ b then .identity true false  -- a ⊆ b: a ∩ b = a (self)
    else if b ⊆ a then .identity false true  -- b ⊆ a: a ∩ b = b (other)
    else .element (a ∩ b)
  psubtract a b :=
    if (a \ b).card = 0 then .none
    else if a ∩ b = ∅ then .identity true false   -- no overlap: a unchanged
    else .element (a \ b)

/-- Join on Finset is commutative at the resolved-value level. -/
instance {α : Type*} [DecidableEq α] : JoinComm (Finset α) where
  pjoin_comm a b := by
    simp only [PathMapLattice.pjoin, AlgebraicResult.resolve]
    by_cases h1 : a = b
    · simp [h1]
    · have h1' : ¬ b = a := fun h => h1 h.symm
      by_cases h2 : a ⊆ b
      · have h3 : ¬ b ⊆ a := fun h => h1 (Finset.Subset.antisymm h2 h)
        simp [h1, h2, h3, h1']
      · by_cases h3 : b ⊆ a
        · simp [h1, h2, h3, h1']
        · simp [h1, h2, h3, h1', Finset.union_comm a b]

/-- Meet on Finset is commutative at the resolved-value level. -/
instance {α : Type*} [DecidableEq α] : MeetComm (Finset α) where
  pmeet_comm a b := by
    simp only [PathMapLattice.pmeet, AlgebraicResult.resolve]
    by_cases h0 : (a ∩ b).card = 0
    · have h0' : (b ∩ a).card = 0 := by rwa [Finset.inter_comm]
      simp [h0, h0']
    · have h0' : ¬ (b ∩ a).card = 0 := by rwa [Finset.inter_comm]
      simp only [h0, h0', ite_false]
      by_cases h1 : a = b
      · simp [h1]
      · have h1' : ¬ b = a := fun h => h1 h.symm
        by_cases h2 : a ⊆ b
        · have h2' : ¬ b ⊆ a := fun h => h1 (Finset.Subset.antisymm h2 h)
          simp [h1, h1', h2, h2']
        · by_cases h3 : b ⊆ a
          · simp [h1, h1', h2, h3]
          · simp [h1, h1', h2, h3, Finset.inter_comm a b]

/-- Join on Finset is idempotent (never produces a new element). -/
instance {α : Type*} [DecidableEq α] : JoinIdem (Finset α) where
  pjoin_idem a := by simp [PathMapLattice.pjoin, AlgebraicResult.isElem]

/-- Meet on Finset is idempotent (never produces a new element).
    When `a = ∅`, `pmeet ∅ ∅ = None` (empty intersection); not a new element.
    When `a ≠ ∅`, `pmeet a a = Identity` (reuses `a`); not a new element. -/
instance {α : Type*} [DecidableEq α] : MeetIdem (Finset α) where
  pmeet_idem a := by
    simp only [PathMapLattice.pmeet, Finset.inter_self, AlgebraicResult.isElem]
    by_cases h : Finset.card a = 0
    · simp [h]
    · simp [h]

/-- Absorption on Finset: join absorbs meet.
    `pjoin a (pmeet a b) = a` at the resolved-value level. -/
instance {α : Type*} [DecidableEq α] : Absorption (Finset α) where
  join_absorbs_meet a b m hm := by
    simp only [PathMapLattice.pmeet, AlgebraicResult.resolve] at hm
    by_cases h0 : (a ∩ b).card = 0
    · simp [h0] at hm
    · simp only [h0, ite_false] at hm
      by_cases h1 : a = b
      · -- pmeet a a = .identity true true → m = a
        subst h1
        simp only [ite_true] at hm
        obtain ⟨rfl⟩ := Option.some.inj hm
        simp [PathMapLattice.pjoin, AlgebraicResult.resolve]
      · by_cases h2 : a ⊆ b
        · -- pmeet: a ⊆ b case → .identity true false → m = a
          simp only [h1, ite_false, h2, ite_true] at hm
          obtain ⟨rfl⟩ := Option.some.inj hm
          simp [PathMapLattice.pjoin, AlgebraicResult.resolve]
        · by_cases h3 : b ⊆ a
          · -- pmeet: b ⊆ a case → .identity false true → m = b
            simp only [h1, ite_false, h2, ite_false, h3, ite_true] at hm
            obtain ⟨rfl⟩ := Option.some.inj hm
            -- pjoin a b with ¬a = b, ¬a ⊆ b, b ⊆ a → .identity true false → some a
            simp only [PathMapLattice.pjoin, AlgebraicResult.resolve, h1, ite_false, h2, ite_false, h3, ite_true]
          · -- pmeet: neither subset → .element (a ∩ b) → m = a ∩ b
            simp only [h1, ite_false, h2, ite_false, h3, ite_false] at hm
            obtain ⟨rfl⟩ := Option.some.inj hm
            -- pjoin a (a ∩ b): a ∩ b ⊆ a always, a ≠ a ∩ b (since ¬a ⊆ b), a ⊄ a ∩ b
            have hsub : a ∩ b ⊆ a := Finset.inter_subset_left
            have hneq : ¬ a = a ∩ b := fun h => h2 (h ▸ Finset.inter_subset_right)
            have hnotasub : ¬ a ⊆ a ∩ b :=
              fun h => h2 (Finset.Subset.trans h Finset.inter_subset_right)
            simp only [PathMapLattice.pjoin, AlgebraicResult.resolve,
                       hneq, ite_false, hnotasub, ite_false, hsub, ite_true]

/-! ## Concrete Instance: `Finset α` Quantale -/

/-- The PathMap quantale on finite sets: prefix-filter operation.

    For finite sets (which are "flat" — elements are atomic, not paths),
    `prestrict a b` retains only elements of `a` that appear in `b`.
    This models the set-level degenerate case of prefix filtering
    (every element is its own single-byte path, so "prefix in b" = "in b").

    - `.identity true false` : `a ⊆ b`  (a is already within b's domain)
    - `.none`                : `a ∩ b = ∅` (no overlap; result is bottom)
    - `.element (a ∩ b)`    : partial overlap -/
instance {α : Type*} [DecidableEq α] : PathMapQuantale (Finset α) where
  prestrict a b :=
    if a ⊆ b then .identity true false
    else if (a ∩ b).card = 0 then .none
    else .element (a ∩ b)

/-! ## Well-formedness of operations on `Finset α` -/

/-- `pjoin` on `Finset α` never produces `.identity false false`. -/
theorem pjoin_wellFormed {α : Type*} [DecidableEq α] (a b : Finset α) :
    AlgebraicResult.WellFormed a b (PathMapLattice.pjoin a b) := by
  simp only [PathMapLattice.pjoin, AlgebraicResult.WellFormed]
  split_ifs <;> simp

/-- `pmeet` on `Finset α` never produces `.identity false false`. -/
theorem pmeet_wellFormed {α : Type*} [DecidableEq α] (a b : Finset α) :
    AlgebraicResult.WellFormed a b (PathMapLattice.pmeet a b) := by
  simp only [PathMapLattice.pmeet, AlgebraicResult.WellFormed]
  split_ifs <;> simp

/-- `psubtract` on `Finset α` never produces `.identity false false`. -/
theorem psubtract_wellFormed {α : Type*} [DecidableEq α] (a b : Finset α) :
    AlgebraicResult.WellFormed a b (PathMapDistributiveLattice.psubtract a b) := by
  simp only [PathMapDistributiveLattice.psubtract, AlgebraicResult.WellFormed]
  split_ifs <;> simp

/-- `prestrict` on `Finset α` never produces `.identity false false`. -/
theorem prestrict_wellFormed {α : Type*} [DecidableEq α] (a b : Finset α) :
    AlgebraicResult.WellFormed a b (PathMapQuantale.prestrict a b) := by
  simp only [PathMapQuantale.prestrict, AlgebraicResult.WellFormed]
  split_ifs <;> simp

/-! ## Quantale associativity for `Finset α` -/

/-- Associativity of prefix restriction at the resolved-value level.

    If `prestrict a b` resolves to `ab`, then restricting `ab` by `c` yields
    the same resolved value as restricting `a` by `b ∩ c` directly.

    This is the key quantale coherence property: sequential restriction
    composes as intersection of filter sets. -/
theorem prestrict_assoc {α : Type*} [DecidableEq α] (a b c : Finset α)
    (ab : Finset α) (h : (PathMapQuantale.prestrict a b).resolve a b = some ab) :
    (PathMapQuantale.prestrict ab c).resolve ab c =
    (PathMapQuantale.prestrict a (b ∩ c)).resolve a (b ∩ c) := by
  by_cases h1 : a ⊆ b
  · -- prestrict a b = .identity true false → ab = a
    have hab : (PathMapQuantale.prestrict a b).resolve a b = some a := by
      simp [PathMapQuantale.prestrict, AlgebraicResult.resolve, h1]
    rw [hab] at h; obtain ⟨rfl⟩ := Option.some.inj h
    have hbc : a ∩ (b ∩ c) = a ∩ c := by
      rw [← Finset.inter_assoc, Finset.inter_eq_left.mpr h1]
    simp only [PathMapQuantale.prestrict, AlgebraicResult.resolve, hbc]
    by_cases h2 : a ⊆ c
    · simp [h2, Finset.subset_inter h1 h2]
    · have h2' : ¬ a ⊆ b ∩ c := fun h => h2 (Finset.subset_inter_iff.mp h).2
      by_cases h3 : (a ∩ c).card = 0
      · simp [h2, h3, h2']
      · simp [h2, h3, h2']
  · by_cases h2 : (a ∩ b).card = 0
    · exfalso; simp [PathMapQuantale.prestrict, AlgebraicResult.resolve, h1, h2] at h
    · -- prestrict a b = .element (a ∩ b) → ab = a ∩ b
      have hab : (PathMapQuantale.prestrict a b).resolve a b = some (a ∩ b) := by
        simp [PathMapQuantale.prestrict, AlgebraicResult.resolve, h1, h2]
      rw [hab] at h; obtain ⟨rfl⟩ := Option.some.inj h
      have key : a ∩ b ∩ c = a ∩ (b ∩ c) := Finset.inter_assoc a b c
      have hne_ab : ¬ a ⊆ b ∩ c := fun h => h1 (Finset.subset_inter_iff.mp h).1
      by_cases h3 : a ∩ b ⊆ c
      · -- LHS: .identity true false → some (a ∩ b)
        -- RHS: .element (a ∩ (b ∩ c)) where a ∩ (b ∩ c) = a ∩ b → some (a ∩ b)
        have h5 : a ∩ (b ∩ c) = a ∩ b := by
          rw [← Finset.inter_assoc]; exact Finset.inter_eq_left.mpr h3
        -- Use h2 (¬(a ∩ b).card = 0) after h5 rewrites a ∩ (b ∩ c) → a ∩ b
        simp only [PathMapQuantale.prestrict, AlgebraicResult.resolve,
                   if_pos h3, if_neg hne_ab, h5, if_neg h2]
      · by_cases h4 : (a ∩ b ∩ c).card = 0
        · -- Both sides: none
          have h4' : (a ∩ (b ∩ c)).card = 0 := by rwa [← key]
          simp only [PathMapQuantale.prestrict, AlgebraicResult.resolve,
                     if_neg h3, if_pos h4, if_neg hne_ab, if_pos h4']
        · -- Both sides: some (a ∩ b ∩ c) = some (a ∩ (b ∩ c))
          have h4' : (a ∩ (b ∩ c)).card ≠ 0 := by rwa [← key]
          simp only [PathMapQuantale.prestrict, AlgebraicResult.resolve,
                     if_neg h3, if_neg h4, if_neg hne_ab, if_neg h4']
          exact congrArg some key

/-! ## Unit Tests -/

section Tests

-- AlgebraicResult constructors and map
#guard (AlgebraicResult.element 42).isElem == true
#guard (AlgebraicResult.none : AlgebraicResult Nat).isNone == true
#guard (AlgebraicResult.identity true false : AlgebraicResult Nat).isIdent == true

-- swapIdent is an involution
example (r : AlgebraicResult Nat) : r.swapIdent.swapIdent = r := by
  simp [AlgebraicResult.swapIdent_swapIdent]

-- Bool join: false ⊔ true = true (COUNTER_IDENT = other)
#guard (PathMapLattice.pjoin false true : AlgebraicResult Bool) == .identity false true
-- Bool join: true ⊔ false = true (SELF_IDENT = self)
#guard (PathMapLattice.pjoin true false : AlgebraicResult Bool) == .identity true false
-- Bool join: false ⊔ false = false (SELF_IDENT = self = false)
#guard (PathMapLattice.pjoin false false : AlgebraicResult Bool) == .identity true false
-- Bool join: true ⊔ true = true (SELF_IDENT = self = true)
#guard (PathMapLattice.pjoin true true : AlgebraicResult Bool) == .identity true false

-- Bool meet: true ∧ false = false (COUNTER_IDENT = other = false)
#guard (PathMapLattice.pmeet true false : AlgebraicResult Bool) == .identity false true
-- Bool meet: true ∧ true = true (SELF_IDENT = self = true)
#guard (PathMapLattice.pmeet true true : AlgebraicResult Bool) == .identity true false

-- JoinComm holds for Bool
example : JoinComm Bool := inferInstance
-- MeetComm holds for Bool
example : MeetComm Bool := inferInstance

end Tests

end Mettapedia.PathMap
