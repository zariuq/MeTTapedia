import Provenance.Util.ValueTypeString
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Generated names, and telling them apart

A generator that mints metavariables from an index — `chan0`, `obsArg2`,
`Tuple3` — needs those names to be distinguishable before anything it builds can
be reasoned about: a rule whose metavariables collide binds the wrong thing, and
a slot family with repetitions counts wrong.

The fact underneath is that decimal printing of a natural number is injective,
which the decoder in `Provenance.Util.ValueTypeString` gives.  This module is
where that lives for name generation, so a presentation's metatheory does not
have to reach into a provenance utility for it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.DecimalNames

/-- Decimal printing of a natural number is injective: the decoder is a left
inverse. -/
theorem repr_injective : Function.Injective Nat.repr := by
  intro first second same
  have firstRound := natStringValue_repr first
  have secondRound := natStringValue_repr second
  rw [same] at firstRound
  exact firstRound.symm.trans secondRound

/-- A name minted by prefixing a decimal index determines the index. -/
theorem prefixed_injective (start : String) {first second : Nat}
    (same : start ++ toString first = start ++ toString second) : first = second := by
  have lists : (start ++ toString first).toList = (start ++ toString second).toList :=
    congrArg String.toList same
  rw [String.toList_append, String.toList_append] at lists
  exact repr_injective (String.ext (List.append_cancel_left lists))

/-- Two names minted from different literal prefixes are different, whatever
their indices, when the prefixes already differ as character lists. -/
theorem literal_ne {leftStart rightStart : String}
    {leftChars rightChars : List Char}
    (leftLiteral : leftStart.toList = leftChars)
    (rightLiteral : rightStart.toList = rightChars)
    (differ : ∀ leftTail rightTail : List Char,
      leftChars ++ leftTail ≠ rightChars ++ rightTail)
    (leftSuffix rightSuffix : String) :
    leftStart ++ leftSuffix ≠ rightStart ++ rightSuffix := by
  intro same
  have lists : (leftStart ++ leftSuffix).toList = (rightStart ++ rightSuffix).toList :=
    congrArg String.toList same
  rw [String.toList_append, String.toList_append, leftLiteral, rightLiteral] at lists
  exact differ leftSuffix.toList rightSuffix.toList lists

/-- A generated name is not a fixed literal when its prefix already differs. -/
theorem prefixed_ne_literal (start fixedLabel suffix : String)
    (differ : ∀ tail : List Char, start.toList ++ tail ≠ fixedLabel.toList) :
    start ++ suffix ≠ fixedLabel := by
  intro same
  have lists : (start ++ suffix).toList = fixedLabel.toList := congrArg String.toList same
  rw [String.toList_append] at lists
  exact differ suffix.toList lists

/-- **A prefixed decimal enumeration has no repetitions.** -/
theorem prefixed_range_nodup (start : String) (bound : Nat) :
    (((List.range bound).map fun index => start ++ toString index)).Nodup := by
  refine List.Nodup.map ?_ (List.nodup_range)
  intro first second same
  exact prefixed_injective start same

end Mettapedia.OSLF.MeTTaIL.DecimalNames
