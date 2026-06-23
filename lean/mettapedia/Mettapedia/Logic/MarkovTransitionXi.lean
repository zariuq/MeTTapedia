import Mettapedia.Logic.WMMarkovCanonical
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.OSLFEvidenceSemantics

/-!
# Direct Xi Surface for Markov Transition Atoms

This module packages the honest single-step Markov WM/PLN bridge into a small
OSLF/Xi-facing surface.

Design choice:

* atom label: a fixed transition predicate name,
* payload pattern: an explicit `link(src,dst)` shape,
* semantics: direct single-step transition evidence extraction,
* no generic deduction/source/sink screening claims.

Positive example:
* `link(i,j)` reads exactly the `i`-row evidence and projects to `j` vs not-`j`.

Negative example:
* this surface does not claim that `link(i,j)` and `link(j,m)` compose via the
  generic PLN additive screening rules.
-/

namespace Mettapedia.Logic.MarkovTransitionXi

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.WMMarkovCanonical
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped ENNReal

variable {k : ℕ} [NeZero k]

/-- Fixed atom label for the direct Markov transition Xi surface. -/
def markovTransitionAtomName : String := "markov-transition"

/-- Pattern payload for a single-step Markov transition query. -/
def markovTransitionAtomPattern (src dst : Fin k) : Pattern :=
  .apply "link" [.bvar src.1, .bvar dst.1]

/-- Parse a `link(src,dst)` pattern payload into Markov transition endpoints. -/
def markovTransitionEndpoints? : Pattern → Option (Fin k × Fin k)
  | .apply "link" [.bvar src, .bvar dst] =>
      if hsrc : src < k then
        if hdst : dst < k then
          some (⟨src, hsrc⟩, ⟨dst, hdst⟩)
        else
          none
      else
        none
  | _ => none

/-- Total fallback query used when an atom/pattern does not encode a Markov
transition. This keeps the encoder total without pretending malformed payloads
have special semantics. -/
def markovTransitionFallbackQuery : MarkovTransitionQuery k :=
  .prop 0

/-- Concrete OSLF atom encoder for the direct Markov Xi surface. -/
def markovTransitionQueryOfAtom :
    String → Pattern → MarkovTransitionQuery k
  | a, p =>
      if a = markovTransitionAtomName then
        match markovTransitionEndpoints? (k := k) p with
        | some (src, dst) => .link src dst
        | none => markovTransitionFallbackQuery (k := k)
      else
        markovTransitionFallbackQuery (k := k)

omit [NeZero k] in
@[simp] theorem markovTransitionEndpoints?_pattern
    (src dst : Fin k) :
    markovTransitionEndpoints? (k := k) (markovTransitionAtomPattern src dst) =
      some (src, dst) := by
  simp [markovTransitionAtomPattern, markovTransitionEndpoints?, src.is_lt, dst.is_lt]

@[simp] theorem markovTransitionQueryOfAtom_link
    (src dst : Fin k) :
    markovTransitionQueryOfAtom (k := k)
        markovTransitionAtomName
        (markovTransitionAtomPattern src dst) =
      .link src dst := by
  simp [markovTransitionQueryOfAtom]

/-- Public XiPLN query surface for direct Markov transition atoms. The rule
sets are intentionally empty here: the value is the concrete encoder and the
direct WM/OSLF semantics, not generic additive screening rules. -/
def markovTransitionXiPLN :
    XiPLN
      (State := MarkovTransitionWMState k)
      (Query := MarkovTransitionQuery k) where
  queryOfAtom := markovTransitionQueryOfAtom (k := k)
  rulesE := ∅
  rulesS := ∅

@[simp] theorem markovTransitionXiPLN_queryOfAtom_link
    (src dst : Fin k) :
    (markovTransitionXiPLN (k := k)).queryOfAtom
        markovTransitionAtomName
        (markovTransitionAtomPattern src dst) =
      .link src dst :=
  markovTransitionQueryOfAtom_link (k := k) src dst

/-- Direct OSLF atom semantics for a well-formed Markov transition atom reads
exactly the binary projection of the source row onto the target state. -/
theorem markovTransitionAtom_semE_eq_rowProjection
    (R : Pattern → Pattern → Prop)
    (W : MarkovTransitionWMState k)
    (src dst : Fin k) :
    semE R
        (wmEvidenceAtomSemQ W ((markovTransitionXiPLN (k := k)).queryOfAtom))
        (.atom markovTransitionAtomName)
        (markovTransitionAtomPattern src dst) =
      markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract (k := k) W src) dst := by
  rw [show
    semE R
        (wmEvidenceAtomSemQ W ((markovTransitionXiPLN (k := k)).queryOfAtom))
        (.atom markovTransitionAtomName)
        (markovTransitionAtomPattern src dst) =
    BinaryWorldModel.evidence
      (State := MarkovTransitionWMState k)
      (Query := MarkovTransitionQuery k)
      W
      (((markovTransitionXiPLN (k := k)).queryOfAtom)
        markovTransitionAtomName
        (markovTransitionAtomPattern src dst)) by
          rfl]
  rw [markovTransitionXiPLN_queryOfAtom_link (k := k) src dst]
  change markov_queryBinaryEvidence (k := k) W (.link src dst) =
    markov_binaryEvidenceOfRowEvidence (markov_rowExtract (k := k) W src) dst
  rfl

/-- Strength-level restatement of the direct Markov transition atom semantics. -/
theorem markovTransitionAtom_queryStrength_eq_rowProjection
    {k : ℕ}
    (W : MarkovTransitionWMState k)
    (src dst : Fin k) :
    BinaryWorldModel.queryStrength
        (State := MarkovTransitionWMState k)
        (Query := MarkovTransitionQuery k)
        W
        (.link src dst) =
     BinaryEvidence.toStrength
      (markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract (k := k) W src) dst) := by
  unfold BinaryWorldModel.queryStrength
  rw [show
    BinaryWorldModel.evidence
      (State := MarkovTransitionWMState k)
      (Query := MarkovTransitionQuery k)
      W
      (.link src dst) =
    markov_binaryEvidenceOfRowEvidence
      (markov_rowExtract (k := k) W src) dst by
        change markov_queryBinaryEvidence (k := k) W (.link src dst) =
          markov_binaryEvidenceOfRowEvidence (markov_rowExtract (k := k) W src) dst
        rfl]

/-- Direct WM evidence for a well-formed Markov transition atom agrees with the
row-conditioned binary projection selected by the encoded link query. -/
theorem markovTransitionAtom_wmEvidence_eq_rowProjection
    (W : MarkovTransitionWMState k)
    (src dst : Fin k) :
      BinaryWorldModel.evidence
          (State := MarkovTransitionWMState k)
          (Query := MarkovTransitionQuery k)
          W
          ((markovTransitionXiPLN (k := k)).queryOfAtom
            markovTransitionAtomName
            (markovTransitionAtomPattern src dst)) =
          markov_binaryEvidenceOfRowEvidence
            (markov_rowExtract (k := k) W src) dst := by
  rw [markovTransitionXiPLN_queryOfAtom_link (k := k) src dst]
  change markov_queryBinaryEvidence (k := k) W (.link src dst) =
    markov_binaryEvidenceOfRowEvidence (markov_rowExtract (k := k) W src) dst
  rfl

/-- On a transition-summary multiset, the direct Markov Xi atom semantics agree
with the row evidence selected by the summary counts. -/
theorem markovTransitionAtom_semE_transitionMultiset_eq_of_summary
    {xs : List (Fin k)}
    {c : Mettapedia.Logic.UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum :
      Mettapedia.Logic.UniversalPrediction.TransCounts.summary (k := k) xs =
        some (c, last))
    (R : Pattern → Pattern → Prop)
    (src dst : Fin k) :
    semE R
        (wmEvidenceAtomSemQ
          (markov_transitionMultiset (k := k) xs)
          ((markovTransitionXiPLN (k := k)).queryOfAtom))
          (.atom markovTransitionAtomName)
          (markovTransitionAtomPattern src dst) =
          markov_binaryEvidenceOfRowEvidence (markov_rowEvidence c src) dst := by
  rw [markovTransitionAtom_semE_eq_rowProjection (k := k)]
  rw [markov_rowExtract_transitionMultiset_eq_rowEvidence_of_summary (k := k) hsum src]

/-- Threshold truth for a direct Markov transition atom follows from the
corresponding row-projected binary evidence. -/
theorem markovTransitionAtom_threshold_of_summary
    {xs : List (Fin k)}
    {c : Mettapedia.Logic.UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum :
      Mettapedia.Logic.UniversalPrediction.TransCounts.summary (k := k) xs =
        some (c, last))
    (R : Pattern → Pattern → Prop)
    (tau : ℝ≥0∞)
    (src dst : Fin k)
    (hTau :
      tau ≤ BinaryEvidence.toStrength
        (markov_binaryEvidenceOfRowEvidence (markov_rowEvidence c src) dst)) :
    sem R
      (thresholdAtomSemOfWMQ
        (markov_transitionMultiset (k := k) xs)
        tau
        ((markovTransitionXiPLN (k := k)).queryOfAtom))
      (.atom markovTransitionAtomName)
      (markovTransitionAtomPattern src dst) := by
  change
    tau ≤ BinaryEvidence.toStrength
      (BinaryWorldModel.evidence
        (State := MarkovTransitionWMState k)
        (Query := MarkovTransitionQuery k)
        (markov_transitionMultiset (k := k) xs)
        ((markovTransitionXiPLN (k := k)).queryOfAtom
          markovTransitionAtomName
          (markovTransitionAtomPattern src dst)))
  rw [markovTransitionXiPLN_queryOfAtom_link (k := k) src dst]
  simpa using
    (show
      tau ≤ BinaryEvidence.toStrength
        (BinaryWorldModel.evidence
          (State := MarkovTransitionWMState k)
          (Query := MarkovTransitionQuery k)
          (markov_transitionMultiset (k := k) xs)
          (.link src dst)) from by
        rw [markov_linkEvidence_transitionMultiset_eq_of_summary (k := k) hsum src dst]
        exact hTau)

end Mettapedia.Logic.MarkovTransitionXi
