import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
import Mettapedia.OSLF.Framework.WMCalculusSemantics
import Mettapedia.OSLF.Framework.WMCalculusZeroBoundary
import Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra

/-!
# Additive world models are readings of the world-model calculus

An additive world model revises states by addition and extracts evidence in
a commutative monoid, with extraction additive over revision.  That is
exactly what the world-model calculus needs of a reading: the calculus's
core laws are the additivity of extraction and the commutative-monoid laws
of evidence.  So every additive world model is a reading satisfying the core
laws, and every rewrite of the calculus, at any depth, preserves meaning in
it (`additive_contextStepStar_agrees`).

Multiplicity spaces are an additive world model: union adds multiplicities,
and counting weighted answers is additive over union
(`SpaceQueryAlgebra.weightedAnswers_union`).  So the calculus is sound for
spaces (`space_contextStepStar_preserves_weightedAnswers`).
For these spaces, empty-state extraction is zero as well
(`space_extract_zero`), using cancellation of natural-number evidence.
That extra law does not follow for arbitrary WM core readings.

Two controls mark the boundary:

* meet of spaces is not a revision for which counting is additive
  (`space_meet_not_additive`);
* counting pairs of answers to two patterns, the shape of a conjunctive
  query without shared variables, is not additive over union: union
  contributes cross terms (`pairCount_union`, `pairCount_not_additive`).
  Semiring-valued provenance can account for these terms, but the query
  interpretation must also satisfy the corresponding join/cross-term law.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra

/-! ## Additive world models as readings -/

section Additive

variable {State Query Ev : Type} [EvidenceType State] [AddCommMonoid Ev]
  [AdditiveWorldModel State Query Ev]

/-- The reading of the calculus in an additive world model: revision and
combination are addition, and state and query atoms are interpreted by the
given valuations. -/
def additiveReading (world : String → State) (query : String → Query) :
    WMReading State Query Ev where
  revise := (· + ·)
  extract := AdditiveWorldModel.extract
  combine := (· + ·)
  zero := 0
  world := world
  query := query

theorem additiveReading_coreLaws (world : String → State) (query : String → Query) :
    (additiveReading (Ev := Ev) world query).CoreLaws where
  extract_revise first second query' :=
    AdditiveWorldModel.extract_add first second query'
  combine_comm := add_comm
  combine_assoc := add_assoc
  combine_zero := add_zero

/-- Every rewrite of the calculus, at any depth and after any number of steps,
preserves meaning in an additive world model. -/
theorem additive_contextStepStar_agrees (world : String → State) (query : String → Query)
    {s : WMSort} {source target : WMTerm s} (steps : WMContextStepStar source target) :
    (additiveReading (Ev := Ev) world query).Agree s
      ((additiveReading world query).denote source)
      ((additiveReading world query).denote target) :=
  (additiveReading_coreLaws world query).agree_of_contextStepStar steps

end Additive

/-! ## Multiplicity spaces -/

section Spaces

variable {Atom : Type}

instance : EvidenceType (MSpace Atom) := {}

/-- A query is read by the list of atoms that answer it; its evidence in a
space is the total multiplicity of those atoms. -/
instance : AdditiveWorldModel (MSpace Atom) (List Atom) ℕ where
  extract := weightedAnswers
  extract_add first second candidates := weightedAnswers_union first second candidates

theorem space_revise_eq_sUnion (first second : MSpace Atom) :
    first + second = sUnion first second := rfl

/-- Unlike an arbitrary WM core reading, multiplicity spaces do extract zero
evidence from the empty state: Nat evidence combination is cancellative. -/
theorem space_extract_zero
    (world : String → MSpace Atom) (query : String → List Atom)
    (candidates : List Atom) :
    (additiveReading (Ev := ℕ) world query).extract (0 : MSpace Atom) candidates =
      (additiveReading (Ev := ℕ) world query).zero := by
  exact Mettapedia.OSLF.Framework.WMCalculusZeroBoundary.extractZero_of_leftCancel
    (additiveReading (Ev := ℕ) world query)
    (additiveReading_coreLaws world query)
    (0 : MSpace Atom)
    (by intro state; simp [additiveReading])
    (by intro first second third equality; exact Nat.add_left_cancel equality)
    candidates

/-- Every rewrite of the calculus preserves weighted answer counts when its
state atoms are spaces and its query atoms are candidate lists. -/
theorem space_contextStepStar_preserves_weightedAnswers
    (world : String → MSpace Atom) (query : String → List Atom)
    {source target : WMTerm .evidence} (steps : WMContextStepStar source target) :
    (additiveReading (Ev := ℕ) world query).denote source =
      (additiveReading (Ev := ℕ) world query).denote target :=
  additive_contextStepStar_agrees (Ev := ℕ) world query steps

/-- Meet keeps the smaller multiplicity, so counting is not additive over it:
meet is not a revision of the calculus. -/
theorem space_meet_not_additive :
    ∃ (first second : MSpace Unit) (candidates : List Unit),
      weightedAnswers (sMeet first second) candidates ≠
        weightedAnswers first candidates + weightedAnswers second candidates := by
  refine ⟨fun _ => 1, fun _ => 1, [()], ?_⟩
  decide

/-- The number of answer pairs to two patterns, with no variables shared
between them, in one space. -/
def pairCount (space : MSpace Atom) (first second : List Atom) : ℕ :=
  weightedAnswers space first * weightedAnswers space second

/-- Over a union, pair counts expand into the pairs within each space plus
the cross pairs that take one answer from each. -/
theorem pairCount_union (left right : MSpace Atom) (first second : List Atom) :
    pairCount (sUnion left right) first second =
      pairCount left first second + pairCount right first second +
        (weightedAnswers left first * weightedAnswers right second +
          weightedAnswers right first * weightedAnswers left second) := by
  unfold pairCount
  rw [weightedAnswers_union, weightedAnswers_union]
  ring

/-- Negative control: pair counts are not additive over union, because of
the cross pairs. -/
theorem pairCount_not_additive :
    ∃ (left right : MSpace Unit) (first second : List Unit),
      pairCount (sUnion left right) first second ≠
        pairCount left first second + pairCount right first second := by
  refine ⟨fun _ => 1, fun _ => 1, [()], [()], ?_⟩
  decide

end Spaces

end Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

#print axioms Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.additiveReading_coreLaws
#print axioms Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.additive_contextStepStar_agrees
#print axioms
  Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.space_contextStepStar_preserves_weightedAnswers
#print axioms Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.space_meet_not_additive
#print axioms Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.pairCount_union
#print axioms Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.pairCount_not_additive
