import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalityControls

/-!
# Controls: past modalities and quantifiers over a type, as proof terms of the package

Each verdict on the representatives is computed by the kernel, read among the hereditarily finite sets by the
verdict's exactness, and turned into a closed proof term of the package: of the proposition when it holds, of its
negation when it fails.

- Proved: some set containing `0` has a member with a member; every set containing `0` has a member; every set
  containing `2` has a member with a member with a member; some set has a member and only empty members; every set
  has a member or none; some set of sets has a member with a member.
- Refuted: some set containing `0` is empty; every set containing `0` has a member with a member (`{0}` does not);
  some set is empty and has a member; every set has a member (`0` does not); some set has a base type other than
  `Set`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Has a member or has none. -/
def inhabitedOrEmpty : Formula 0 := .or inhabited emptySet

/-- Has a member with a member with a member. -/
def deeper : Formula 0 := .possibly .any deep

/-! ## The verdicts, computed by the kernel -/

theorem verdict_zero_deep : pastVerdict (.sometimeBefore .any deep) zero = true := by decide +kernel
theorem verdict_zero_empty : pastVerdict (.sometimeBefore .any emptySet) zero = false := by decide +kernel
theorem verdict_zero_every_inhabited : pastVerdict (.alwaysBefore .any inhabited) zero = true := by decide +kernel
theorem verdict_zero_every_deep : pastVerdict (.alwaysBefore .any deep) zero = false := by decide +kernel
theorem verdict_two_every_deeper : pastVerdict (.alwaysBefore .any deeper) two = true := by decide +kernel
theorem verdict_some_empty_members :
    pastVerdict (.someOf (.base "Set") (.and inhabited (.necessarily .any emptySet))) zero = true := by decide +kernel
theorem verdict_some_empty_inhabited : pastVerdict (.someOf (.base "Set") (.and emptySet inhabited)) zero = false := by
  decide +kernel
theorem verdict_every_inhabited : pastVerdict (.everyOf (.base "Set") inhabited) zero = false := by decide +kernel
theorem verdict_every_inhabited_or_empty : pastVerdict (.everyOf (.base "Set") inhabitedOrEmpty) zero = true := by
  decide +kernel
theorem verdict_some_sets_deep : pastVerdict (.someOf (.collection .hashSet (.base "Set")) deep) zero = true := by
  decide +kernel
theorem verdict_some_atom : pastVerdict (.someOf (.base "Atom") .top) zero = false := by decide +kernel

/-! ## What they mean among the hereditarily finite sets -/

/-- **Every set containing `2` has a member with a member with a member**: `2` itself. -/
theorem two_every_deeper : HFSets.sat Env.closed (.alwaysBefore .any deeper) (hfOf two_hf) :=
  (pastVerdict_iff rfl two_hf).mp verdict_two_every_deeper

/-- **Every set has a member or has none.** -/
theorem every_inhabited_or_empty :
    HFSets.sat Env.closed (.everyOf (.base "Set") inhabitedOrEmpty) (hfOf zero_hf) :=
  (pastVerdict_iff rfl zero_hf).mp verdict_every_inhabited_or_empty

/-- **Not every set containing `0` has a member with a member.** -/
theorem not_zero_every_deep : ¬ HFSets.sat Env.closed (.alwaysBefore .any deep) (hfOf zero_hf) := fun holds => by
  have verdict := (pastVerdict_iff rfl zero_hf).mpr holds
  rw [verdict_zero_every_deep] at verdict
  exact Bool.false_ne_true verdict

/-- **No set has the base type `Atom`.** -/
theorem no_atom : ¬ HFSets.sat Env.closed (.someOf (.base "Atom") .top) (hfOf zero_hf) := fun holds => by
  have verdict := (pastVerdict_iff rfl zero_hf).mpr holds
  rw [verdict_some_atom] at verdict
  exact Bool.false_ne_true verdict

/-! ## Closed proof terms of the package -/

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)

variable {L : Type} [LevelOrder L]

/-- A proved past type, as a closed proof term. -/
abbrev ProvedTerm (formula : Formula 0) (term : Pattern) : Prop :=
  ∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))

/-- A refuted past type, as a closed proof term of the negation. -/
abbrev RefutedTerm (formula : Formula 0) (term : Pattern) : Prop :=
  ∃ proofTerm : CTm (Head L) 0,
    CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term)))))

/-- **The proved controls**, each a closed proof term of the package. -/
theorem proved_controls :
    ProvedTerm (L := L) (.sometimeBefore .any deep) zero ∧ ProvedTerm (L := L) (.alwaysBefore .any inhabited) zero ∧
      ProvedTerm (L := L) (.alwaysBefore .any deeper) two ∧
      ProvedTerm (L := L) (.someOf (.base "Set") (.and inhabited (.necessarily .any emptySet))) zero ∧
      ProvedTerm (L := L) (.everyOf (.base "Set") inhabitedOrEmpty) zero ∧
      ProvedTerm (L := L) (.someOf (.collection .hashSet (.base "Set")) deep) zero :=
  ⟨⟨packageTerm (pastSentenceProof lawsOfList rfl zero_hf verdict_zero_deep), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceProof lawsOfList rfl zero_hf verdict_zero_every_inhabited), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceProof lawsOfList rfl two_hf verdict_two_every_deeper), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceProof lawsOfList rfl zero_hf verdict_some_empty_members), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceProof lawsOfList rfl zero_hf verdict_every_inhabited_or_empty), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceProof lawsOfList rfl zero_hf verdict_some_sets_deep), packageTerm_typed _⟩⟩

/-- **The refuted controls**, each a closed proof term of the negation. -/
theorem refuted_controls :
    RefutedTerm (L := L) (.sometimeBefore .any emptySet) zero ∧ RefutedTerm (L := L) (.alwaysBefore .any deep) zero ∧
      RefutedTerm (L := L) (.someOf (.base "Set") (.and emptySet inhabited)) zero ∧
      RefutedTerm (L := L) (.everyOf (.base "Set") inhabited) zero ∧
      RefutedTerm (L := L) (.someOf (.base "Atom") .top) zero :=
  ⟨⟨packageTerm (pastSentenceRefutation lawsOfList rfl zero_hf verdict_zero_empty), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceRefutation lawsOfList rfl zero_hf verdict_zero_every_deep), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceRefutation lawsOfList rfl zero_hf verdict_some_empty_inhabited), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceRefutation lawsOfList rfl zero_hf verdict_every_inhabited), packageTerm_typed _⟩,
    ⟨packageTerm (pastSentenceRefutation lawsOfList rfl zero_hf verdict_some_atom), packageTerm_typed _⟩⟩

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
