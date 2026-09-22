import Mettapedia.OSLF.Framework.GeneratedScope

/-!
# Strata and generator length: the gap the construction is for

A generated scope is a least fixed point, so each of its names is reached after
some number of unfoldings.  The source calls that number the name's **stratum**,
gives atoms stratum zero, and separately defines the **generator length** as the
number of symbols in the formula that generates the scope.

Its point is then that these are not the same kind of quantity and do not move
together: the extension grows while the generator does not grow at all, and the
temptation on meeting a compact description of an enormous structure is to
conclude that the structure is cheap.  It is not -- the description is.

That observation is made a theorem here, in three pieces.

* `stratum_join_le` and `join_injective`: the names at stratum at most `j + 1`
  contain an injective image of the **pairs** of names at stratum at most `j`.
  So each unfolding squares what the previous one reached.
* `stratum_tower`: every stratum is inhabited, so the grading is not eventually
  empty and the squaring is not vacuous.
* `generatorLength`: the generator's size is a function of its two atoms alone.
  It has no argument for the stratum, which is the formal content of "the
  generator does not grow".

The descent these rest on is already in place: quoting a part of a composition is
strictly smaller than quoting the whole.
-/

namespace Mettapedia.OSLF.Framework.ScopeStratum

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GeneratedScope

set_option autoImplicit false

/-! ## Definition 18.3, the stratum -/

/-- **The stratum of a name**: how many unfoldings of the generator are needed
to reach it.  A name that is not a quoted composition is an atom of the
generator and has stratum zero. -/
def stratum : Pattern → Nat
  | .apply "NQuote" [.collection .hashBag [left, right] none] =>
      1 + max (stratum (quote left)) (stratum (quote right))
  | _ => 0
termination_by name => sizeOf name
decreasing_by
  · exact sizeOf_quote_lt_left left right
  · exact sizeOf_quote_lt_right left right

/-- The stratum of a composite, in the formers it is written with. -/
theorem stratum_quote_par (left right : Pattern) :
    stratum (quote (par left right))
      = 1 + max (stratum (quote left)) (stratum (quote right)) := by
  rw [quote, par, stratum]

/-- **Each unfolding raises the stratum by exactly one.**  A composite of two
names at stratum at most `j` sits at stratum at most `j + 1`. -/
theorem stratum_join_le {left right : Pattern} {bound : Nat}
    (leftBounded : stratum (quote left) ≤ bound)
    (rightBounded : stratum (quote right) ≤ bound) :
    stratum (quote (par left right)) ≤ bound + 1 := by
  rw [stratum_quote_par]
  omega

/-! ## The squaring -/

/-- Quoting is injective. -/
theorem quote_injective : Function.Injective quote := by
  intro first second equal
  simpa [quote] using equal

/-- **Joining is injective.**  Two composites are the same name only when their
parts agree, so the pairs of names at one stratum inject into the names at the
next. -/
theorem join_injective :
    Function.Injective (fun parts : Pattern × Pattern => quote (par parts.1 parts.2)) := by
  rintro ⟨leftOne, rightOne⟩ ⟨leftTwo, rightTwo⟩ equal
  have parts := quote_injective equal
  have split : leftOne = leftTwo ∧ rightOne = rightTwo := by
    simpa [par] using parts
  simp [split.1, split.2]

/-! ## Every stratum is inhabited

Without this the squaring could be a statement about empty sets.  The tower
doubles a single atom at each step, and its stratum is exactly its height. -/

/-- The process whose quotation sits at a given stratum. -/
def towerBody (atom : Pattern) : Nat → Pattern
  | 0 => atom
  | height + 1 => par (towerBody atom height) (towerBody atom height)

/-- Its quotation: a name at the given stratum. -/
def tower (atom : Pattern) (height : Nat) : Pattern := quote (towerBody atom height)

/-- **The strata are all inhabited**, provided the atom really is one -- a name
the generator does not already read as a composition. -/
theorem stratum_tower {atom : Pattern} (isAtom : stratum (quote atom) = 0)
    (height : Nat) : stratum (tower atom height) = height := by
  induction height with
  | zero => simpa [tower, towerBody] using isAtom
  | succ previous ih =>
      have : tower atom (previous + 1)
          = quote (par (towerBody atom previous) (towerBody atom previous)) := rfl
      rw [this, stratum_quote_par]
      have unfold : quote (towerBody atom previous) = tower atom previous := rfl
      rw [unfold, ih]
      omega

/-- A constant is an atom of the generator: it is not a quoted composition. -/
theorem stratum_constant (label : String) : stratum (quote (.apply label [])) = 0 := by
  simp [quote, stratum]

/-! ## Definition 18.4, the generator length, and the gap -/

/-- **The generator length**: the symbols of the generating formula together
with the lengths of its two atomic predicates.  The skeleton is a parameter
rather than a literal, because this development's generator is a function rather
than a syntactic formula, and inventing a symbol count for it would be a number
with nothing behind it.  The gap below needs only that the length has no stratum
argument. -/
def generatorLength (skeleton atomLengthA atomLengthB : Nat) : Nat :=
  skeleton + atomLengthA + atomLengthB

/-- Every name has positive size. -/
theorem one_le_sizeOf (name : Pattern) : 1 ≤ sizeOf name := by
  cases name <;> simp +arith

/-- **Each unfolding at least doubles what it describes.** -/
theorem sizeOf_towerBody_succ (atom : Pattern) (height : Nat) :
    2 * sizeOf (towerBody atom height) ≤ sizeOf (towerBody atom (height + 1)) := by
  simp +arith [towerBody, par, Pattern.collection.sizeOf_spec]

/-- **So what the generator describes grows at least exponentially.** -/
theorem two_pow_le_sizeOf_towerBody (atom : Pattern) (height : Nat) :
    2 ^ height ≤ sizeOf (towerBody atom height) := by
  induction height with
  | zero => simpa [towerBody] using one_le_sizeOf atom
  | succ previous ih =>
      have doubled := sizeOf_towerBody_succ atom previous
      have : 2 ^ (previous + 1) = 2 * 2 ^ previous := by ring
      omega

/-- **The gap, as a theorem.**  Past any bound there is a stratum whose
inhabitant is larger, while the generator's length is one number with no stratum
argument at all.  The description is cheap; the structure described is not. -/
theorem description_is_cheap (skeleton atomLengthA atomLengthB : Nat)
    (atom : Pattern) (bound : Nat) :
    ∃ height : Nat,
      generatorLength skeleton atomLengthA atomLengthB
          < sizeOf (towerBody atom height)
        ∧ bound < sizeOf (towerBody atom height) := by
  refine ⟨max (generatorLength skeleton atomLengthA atomLengthB) bound + 1, ?_, ?_⟩
  · have := two_pow_le_sizeOf_towerBody atom
      (max (generatorLength skeleton atomLengthA atomLengthB) bound + 1)
    have lt := Nat.lt_two_pow_self
      (n := max (generatorLength skeleton atomLengthA atomLengthB) bound + 1)
    have le : generatorLength skeleton atomLengthA atomLengthB
        ≤ max (generatorLength skeleton atomLengthA atomLengthB) bound :=
      le_max_left _ _
    omega
  · have := two_pow_le_sizeOf_towerBody atom
      (max (generatorLength skeleton atomLengthA atomLengthB) bound + 1)
    have lt := Nat.lt_two_pow_self
      (n := max (generatorLength skeleton atomLengthA atomLengthB) bound + 1)
    have le : bound ≤ max (generatorLength skeleton atomLengthA atomLengthB) bound :=
      le_max_right _ _
    omega

end Mettapedia.OSLF.Framework.ScopeStratum
