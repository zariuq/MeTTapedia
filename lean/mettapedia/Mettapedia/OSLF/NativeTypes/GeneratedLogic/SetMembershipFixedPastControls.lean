import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPastProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastProofControls

/-!
# Controls: past types with fixed-point bodies, as proof terms of the package

Each verdict on the representatives is computed by the kernel, read among the hereditarily finite sets by the
verdict's exactness, and turned into a closed proof term of the package.

- `fixWellFounded` (`μX. □X`, every descent from the set ends) holds of every hereditarily finite set; `fixEndlessDescent`
  (`νX. ◇X`, an endless descent) of none; `fixReachesEmpty` (`μX. □⊥ ∨ ◇X`, some descent reaches an empty set) of every
  set; `fixLeastDescent` (`μX. ◇X`) of none.
- Proved: some set containing `0` is well-founded; every set containing `0` is well-founded; every set reaches an
  empty set; some set reaches an empty set; every set containing `1` has a descent to a set with an empty member.
- Refuted: some set containing `0` has an endless descent; some set has an endless descent; every set has an endless
  descent; some set containing `0` satisfies `μX. ◇X`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Every descent ends. -/
def fixWellFounded : Formula 0 := .mu (.necessarily .any (.var 0))

/-- Some descent never ends. -/
def fixEndlessDescent : Formula 0 := .nu (.possibly .any (.var 0))

/-- Some descent reaches an empty set. -/
def fixReachesEmpty : Formula 0 := .mu (.or (.necessarily .any .bot) (.possibly .any (.var 0)))

/-- The least fixed point of a step. -/
def fixLeastDescent : Formula 0 := .mu (.possibly .any (.var 0))

/-- Some descent reaches a set with an empty member. -/
def fixReachesEmptyMember : Formula 0 :=
  .mu (.or (.possibly .any (.necessarily .any .bot)) (.possibly .any (.var 0)))

theorem fixOneHolds : IsHF one := (hereditary_iff _).mp (by decide)

/-! ## Admission and verdicts, computed by the kernel -/

theorem admitted_controls :
    (Formula.sometimeBefore .any fixWellFounded).pastFixed = true ∧
      (Formula.alwaysBefore .any fixWellFounded).pastFixed = true ∧
      (Formula.sometimeBefore .any fixEndlessDescent).pastFixed = true ∧
      (Formula.everyOf (.base "Set") fixReachesEmpty).pastFixed = true ∧
      (Formula.someOf (.base "Set") fixReachesEmpty).pastFixed = true ∧
      (Formula.someOf (.base "Set") fixEndlessDescent).pastFixed = true ∧
      (Formula.everyOf (.base "Set") fixEndlessDescent).pastFixed = true ∧
      (Formula.sometimeBefore .any fixLeastDescent).pastFixed = true ∧
      (Formula.alwaysBefore .any fixReachesEmptyMember).pastFixed = true := by
  decide +kernel

theorem fixed_verdict_zero_wellFounded : pastFixedVerdict (.sometimeBefore .any fixWellFounded) zero = true := by
  decide +kernel
theorem fixed_verdict_zero_every_wellFounded : pastFixedVerdict (.alwaysBefore .any fixWellFounded) zero = true := by
  decide +kernel
theorem fixed_verdict_zero_illFounded : pastFixedVerdict (.sometimeBefore .any fixEndlessDescent) zero = false := by
  decide +kernel
theorem fixed_verdict_every_reachesEmpty : pastFixedVerdict (.everyOf (.base "Set") fixReachesEmpty) zero = true := by
  decide +kernel
theorem fixed_verdict_some_reachesEmpty : pastFixedVerdict (.someOf (.base "Set") fixReachesEmpty) zero = true := by
  decide +kernel
theorem fixed_verdict_some_illFounded : pastFixedVerdict (.someOf (.base "Set") fixEndlessDescent) zero = false := by
  decide +kernel
theorem fixed_verdict_every_illFounded : pastFixedVerdict (.everyOf (.base "Set") fixEndlessDescent) zero = false := by
  decide +kernel
theorem fixed_verdict_zero_endless : pastFixedVerdict (.sometimeBefore .any fixLeastDescent) zero = false := by
  decide +kernel
theorem fixed_verdict_one_every_reachesEmptyMember :
    pastFixedVerdict (.alwaysBefore .any fixReachesEmptyMember) one = true := by
  decide +kernel

/-! ## What they mean among the hereditarily finite sets -/

/-- **No set has an endless descent.** -/
theorem no_illFounded_set : ¬ HFSets.sat Env.closed (.someOf (.base "Set") fixEndlessDescent) (hfOf zero_hf) := fun holds => by
  have verdict := (pastFixedVerdict_iff admitted_controls.2.2.2.2.2.1 zero_hf).mpr holds
  rw [fixed_verdict_some_illFounded] at verdict
  exact Bool.false_ne_true verdict

/-- **Every set reaches an empty set.** -/
theorem every_reachesEmpty : HFSets.sat Env.closed (.everyOf (.base "Set") fixReachesEmpty) (hfOf zero_hf) :=
  (pastFixedVerdict_iff admitted_controls.2.2.2.1 zero_hf).mp fixed_verdict_every_reachesEmpty

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

/-- **The proved controls with fixed-point bodies**, each a closed proof term of the package. -/
theorem fixed_proved_controls :
    ProvedTerm (L := L) (.sometimeBefore .any fixWellFounded) zero ∧
      ProvedTerm (L := L) (.alwaysBefore .any fixWellFounded) zero ∧
      ProvedTerm (L := L) (.everyOf (.base "Set") fixReachesEmpty) zero ∧
      ProvedTerm (L := L) (.someOf (.base "Set") fixReachesEmpty) zero ∧
      ProvedTerm (L := L) (.alwaysBefore .any fixReachesEmptyMember) one :=
  ⟨⟨packageTerm (pastFixedSentenceProof lawsOfList admitted_controls.1 zero_hf fixed_verdict_zero_wellFounded),
      packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceProof lawsOfList admitted_controls.2.1 zero_hf fixed_verdict_zero_every_wellFounded),
      packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceProof lawsOfList admitted_controls.2.2.2.1 zero_hf fixed_verdict_every_reachesEmpty),
      packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceProof lawsOfList admitted_controls.2.2.2.2.1 zero_hf fixed_verdict_some_reachesEmpty),
      packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceProof lawsOfList admitted_controls.2.2.2.2.2.2.2.2 fixOneHolds
      fixed_verdict_one_every_reachesEmptyMember), packageTerm_typed _⟩⟩

/-- **The refuted controls with fixed-point bodies**, each a closed proof term of the negation. -/
theorem fixed_refuted_controls :
    RefutedTerm (L := L) (.sometimeBefore .any fixEndlessDescent) zero ∧
      RefutedTerm (L := L) (.someOf (.base "Set") fixEndlessDescent) zero ∧
      RefutedTerm (L := L) (.everyOf (.base "Set") fixEndlessDescent) zero ∧
      RefutedTerm (L := L) (.sometimeBefore .any fixLeastDescent) zero :=
  ⟨⟨packageTerm (pastFixedSentenceRefutation lawsOfList admitted_controls.2.2.1 zero_hf fixed_verdict_zero_illFounded),
      packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceRefutation lawsOfList admitted_controls.2.2.2.2.2.1 zero_hf
      fixed_verdict_some_illFounded), packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceRefutation lawsOfList admitted_controls.2.2.2.2.2.2.1 zero_hf
      fixed_verdict_every_illFounded), packageTerm_typed _⟩,
    ⟨packageTerm (pastFixedSentenceRefutation lawsOfList admitted_controls.2.2.2.2.2.2.2.1 zero_hf
      fixed_verdict_zero_endless), packageTerm_typed _⟩⟩

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
