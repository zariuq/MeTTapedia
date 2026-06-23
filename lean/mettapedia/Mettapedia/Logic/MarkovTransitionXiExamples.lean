import Mettapedia.Logic.MarkovTransitionXi

/-!
# Examples and Consumer Theorems for Direct Markov Xi Transition Atoms

This file gives small concrete examples for the direct Markov Xi query surface
and packages the main semantics as user-facing WM query judgments.
-/

namespace Mettapedia.Logic.MarkovTransitionXiExamples

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.WMMarkovCanonical
open Mettapedia.Logic.MarkovTransitionXi
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped ENNReal

variable {k : ℕ} [NeZero k]

abbrev bit0 : Fin 2 := ⟨0, by decide⟩
abbrev bit1 : Fin 2 := ⟨1, by decide⟩

/-- A concrete binary example pattern encoding the transition `0 → 1`. -/
def bit01Pattern : Pattern :=
  markovTransitionAtomPattern (k := 2) bit0 bit1

/-- A concrete binary example pattern encoding the transition `1 → 0`. -/
def bit10Pattern : Pattern :=
  markovTransitionAtomPattern (k := 2) bit1 bit0

@[simp] theorem bit01Pattern_endpoints :
    markovTransitionEndpoints? (k := 2) bit01Pattern = some (bit0, bit1) := by
  simp [bit01Pattern]

@[simp] theorem bit10Pattern_endpoints :
    markovTransitionEndpoints? (k := 2) bit10Pattern = some (bit1, bit0) := by
  simp [bit10Pattern]

@[simp] theorem bit01Pattern_query :
    (markovTransitionXiPLN (k := 2)).queryOfAtom
        markovTransitionAtomName bit01Pattern =
      .link bit0 bit1 := by
  simp [bit01Pattern, markovTransitionXiPLN_queryOfAtom_link]

@[simp] theorem bit10Pattern_query :
    (markovTransitionXiPLN (k := 2)).queryOfAtom
        markovTransitionAtomName bit10Pattern =
      .link bit1 bit0 := by
  simp [bit10Pattern, markovTransitionXiPLN_queryOfAtom_link]

@[simp] theorem bit01Pattern_wrongLabel_fallback :
    markovTransitionQueryOfAtom (k := 2) "other" bit01Pattern =
      markovTransitionFallbackQuery (k := 2) := by
  simp [markovTransitionQueryOfAtom, markovTransitionAtomName]

/-- Consumer-facing WM judgment for a well-formed transition atom: the encoded
atom query extracts exactly the projected source-row evidence. -/
theorem markovTransitionAtom_queryJudgment
    (W : MarkovTransitionWMState k)
    (src dst : Fin k) :
    ⊢q W ⇓
      ((markovTransitionXiPLN (k := k)).queryOfAtom
        markovTransitionAtomName
        (markovTransitionAtomPattern src dst)) ↦
      markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract (k := k) W src) dst := by
  refine ⟨WMJudgment.axiom W, ?_⟩
  simpa using
    (markovTransitionAtom_wmEvidence_eq_rowProjection (k := k) W src dst).symm

/-- Summary-level consumer theorem: on the transition multiset of a word, the
encoded transition atom extracts the row selected by the Markov summary. -/
theorem markovTransitionAtom_queryJudgment_of_summary
    {xs : List (Fin k)}
    {c : Mettapedia.Logic.UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum :
      Mettapedia.Logic.UniversalPrediction.TransCounts.summary (k := k) xs =
        some (c, last))
    (src dst : Fin k) :
    ⊢q (markov_transitionMultiset (k := k) xs) ⇓
      ((markovTransitionXiPLN (k := k)).queryOfAtom
        markovTransitionAtomName
        (markovTransitionAtomPattern src dst)) ↦
      markov_binaryEvidenceOfRowEvidence (markov_rowEvidence c src) dst := by
  refine ⟨WMJudgment.axiom _, ?_⟩
  rw [markovTransitionXiPLN_queryOfAtom_link (k := k) src dst]
  symm
  simpa using
    markov_linkEvidence_transitionMultiset_eq_of_summary (k := k) hsum src dst

/-- Binary example of the summary-level consumer theorem for the transition
`0 → 1`. -/
theorem bit01_queryJudgment_of_summary
    {xs : List (Fin 2)}
    {c : Mettapedia.Logic.UniversalPrediction.TransCounts 2}
    {last : Fin 2}
    (hsum :
      Mettapedia.Logic.UniversalPrediction.TransCounts.summary (k := 2) xs =
        some (c, last)) :
    ⊢q (markov_transitionMultiset (k := 2) xs) ⇓
      ((markovTransitionXiPLN (k := 2)).queryOfAtom
        markovTransitionAtomName bit01Pattern) ↦
      markov_binaryEvidenceOfRowEvidence (markov_rowEvidence c bit0) bit1 := by
  simpa [bit01Pattern] using
    markovTransitionAtom_queryJudgment_of_summary
      (k := 2) hsum bit0 bit1

end Mettapedia.Logic.MarkovTransitionXiExamples
