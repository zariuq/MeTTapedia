import Mettapedia.Computability.ComputationalTrinity
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Basic

/-!
# Observation-carrier calibration for a computational-trinity comparison

This abstract calibration model compares three common observation carriers:

* an **ordered stream** of answers — the process face, where selection order,
  soft cut, and scheduling are visible;
* a **bag** (multiset) of answer occurrences — the proof-relevant face, where
  multiplicity is retained but order is forgotten;
* a **set** of answers — an extensional face.

The projections `stream ↦ bag ↦ set` form a commuting comparison triangle in
the sense of `ComputationalTrinity.Comparison`.  The comparison is genuinely
not exact: it loses order at the first step and multiplicity at the second,
and both losses are witnessed below.  This is the data-level shadow of the
intensional-to-extensional collapse: an engine that identifies the three
carriers has silently chosen one face.

The model uses constant Boolean presheaves.  It does not by itself establish
an adequacy theorem for HE, PeTTa, CeTTa, MORK, or MM2; each engine requires an
explicit bridge from its actual observation type and execution relation.
-/

namespace Mettapedia.Computability.ObservationCarrierTrinity

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity

abbrev Context := Discrete PUnit

/-- Ordered answer streams. -/
def streamFace : Face Context := (Functor.const Contextᵒᵖ).obj (List Bool)

/-- Answer occurrence bags. -/
def bagFace : Face Context := (Functor.const Contextᵒᵖ).obj (Multiset Bool)

/-- Extensional answer sets. -/
def setFace : Face Context := (Functor.const Contextᵒᵖ).obj (Finset Bool)

/-- Forget order. -/
def streamToBag : streamFace ⟶ bagFace :=
  (Functor.const Contextᵒᵖ).map (↾(fun answers : List Bool => (answers : Multiset Bool)))

/-- Forget multiplicity. -/
def bagToSet : bagFace ⟶ setFace :=
  (Functor.const Contextᵒᵖ).map (↾(fun answers : Multiset Bool => answers.toFinset))

/-- Forget both at once. -/
def streamToSet : streamFace ⟶ setFace :=
  (Functor.const Contextᵒᵖ).map (↾(fun answers : List Bool => answers.toFinset))

/-- The three carriers with their projections form a comparison triangle. -/
def comparison : Comparison Context where
  program := streamFace
  logic := bagFace
  space := setFace
  programToLogic := streamToBag
  logicToSpace := bagToSet
  programToSpace := streamToSet
  coherence := by
    ext context answers
    rfl

private def here : Contextᵒᵖ := Opposite.op (Discrete.mk PUnit.unit)

/-- Order is lost already at the bag: two streams with the same occurrences
in different order are distinct programs with one bag. -/
theorem streamToBag_forgets_order :
    streamToBag.app here [true, false] = streamToBag.app here [false, true] ∧
      ([true, false] : List Bool) ≠ [false, true] := by
  refine ⟨?_, by decide⟩
  show ((([true, false] : List Bool)) : Multiset Bool) = (([false, true] : List Bool) : Multiset Bool)
  decide

/-- Multiplicity is lost at the set: two bags with different occurrence counts
have one set. -/
theorem bagToSet_forgets_multiplicity :
    bagToSet.app here ({true, true} : Multiset Bool) =
        bagToSet.app here ({true} : Multiset Bool) ∧
      ({true, true} : Multiset Bool) ≠ ({true} : Multiset Bool) := by
  refine ⟨?_, by decide⟩
  show ({true, true} : Multiset Bool).toFinset = ({true} : Multiset Bool).toFinset
  decide

/-- Consequently the comparison loses program information: the extensional
face cannot distinguish an ordered stream from its reversal. -/
theorem comparison_losesProgramInformation :
    comparison.LosesProgramInformation := by
  refine ⟨here, [true, false], [false, true],
    (by show ([true, false] : List Bool) ≠ [false, true]; decide), ?_⟩
  show ([true, false] : List Bool).toFinset = ([false, true] : List Bool).toFinset
  decide

/-- No exact trinity has these projections as its interpretation: the
stream-to-set map is not injective. -/
theorem no_compatible_streamSet_iso :
    ¬ ∃ exact : streamFace ≅ setFace, exact.hom = comparison.programToSpace := by
  rintro ⟨exact, agrees⟩
  have same : exact.hom.app here [true, false] = exact.hom.app here [false, true] := by
    rw [agrees]
    show ([true, false] : List Bool).toFinset = ([false, true] : List Bool).toFinset
    decide
  have equal : ([true, false] : List Bool) = [false, true] :=
    (exact.app here).toEquiv.injective same
  exact absurd equal (by decide)

#print axioms comparison
#print axioms streamToBag_forgets_order
#print axioms bagToSet_forgets_multiplicity
#print axioms comparison_losesProgramInformation
#print axioms no_compatible_streamSet_iso

end Mettapedia.Computability.ObservationCarrierTrinity
