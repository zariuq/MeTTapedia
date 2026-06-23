import Mettapedia.Logic.MarkovLogicAbstract
import Mettapedia.Logic.OSLFEvidenceSemantics
import Mettapedia.Logic.WMMarkovCanonical
import Mettapedia.Logic.MarkovPredictiveChaining
import Mettapedia.Logic.PLNWMOSLFBridge

/-!
# Direct Markov Xi Surface for Multi-Step Transition Paths

This file adds an honest `markov-transition*` atom family for multi-step Markov
queries.

The key design choice is to stay on the non-additive perimeter:

* single-step row evidence lives in the additive WM layer;
* multi-step predictive chaining lives in a singleton `MassSemantics` state;
* the path atom semantics therefore compiles to `markovWMPosteriorChain`, not to
  additive carrier pooling.
-/

noncomputable section

namespace Mettapedia.Logic.MarkovPathXi

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.WMMarkovCanonical
open Mettapedia.Logic.MarkovPredictiveChaining
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped ENNReal

variable {k : ℕ} [NeZero k]

/-- Query for a concrete multi-step transition path: start in `start`, then
predict the successive states in `tail`. -/
structure MarkovTransitionPathQuery (k : ℕ) where
  start : Fin k
  tail : List (Fin k)
deriving DecidableEq, Repr

/-- The non-additive singleton semantics state used by the path surface. -/
abbrev MarkovTransitionPathState (k : ℕ) :=
  MassState (MarkovTransitionPathQuery k)

/-- Fixed atom label for direct Markov path queries. -/
def markovTransitionPathAtomName : String := "markov-transition*"

/-- Pattern payload for a Markov path query. The head is the start state; the
remaining entries are the predicted future path. -/
def markovTransitionPathAtomPattern (start : Fin k) (tail : List (Fin k)) : Pattern :=
  .apply "path" ((start :: tail).map fun a => .bvar a.1)

private def decodePathArgs? : List Pattern → Option (List (Fin k))
  | [] => some []
  | .bvar a :: ps =>
      if ha : a < k then
        match decodePathArgs? ps with
        | some tail => some (⟨a, ha⟩ :: tail)
        | none => none
      else
        none
  | _ => none

omit [NeZero k] in
@[simp] theorem decodePathArgs?_map_bvar (xs : List (Fin k)) :
    decodePathArgs? (k := k) (xs.map fun a => Pattern.bvar a.1) = some xs := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simp [decodePathArgs?, a.is_lt, ih]

/-- Parse a `path(i₀, i₁, ..., iₙ)` payload into a start state and future tail. -/
def markovTransitionPathEndpoints? : Pattern → Option (Fin k × List (Fin k))
  | .apply "path" args =>
      match decodePathArgs? (k := k) args with
      | some [] => none
      | some (start :: tail) => some (start, tail)
      | none => none
  | _ => none

omit [NeZero k] in
@[simp] theorem markovTransitionPathEndpoints?_pattern
    (start : Fin k) (tail : List (Fin k)) :
    markovTransitionPathEndpoints? (k := k) (markovTransitionPathAtomPattern start tail) =
      some (start, tail) := by
  unfold markovTransitionPathEndpoints? markovTransitionPathAtomPattern
  simp [decodePathArgs?, start.is_lt, decodePathArgs?_map_bvar (k := k) tail]

/-- Total fallback query used for malformed path atoms. -/
def markovTransitionPathFallbackQuery : MarkovTransitionPathQuery k :=
  ⟨0, []⟩

/-- Concrete OSLF atom encoder for multi-step Markov path queries. -/
def markovTransitionPathQueryOfAtom :
    String → Pattern → MarkovTransitionPathQuery k
  | a, p =>
      if a = markovTransitionPathAtomName then
        match markovTransitionPathEndpoints? (k := k) p with
        | some (start, tail) => ⟨start, tail⟩
        | none => markovTransitionPathFallbackQuery (k := k)
      else
        markovTransitionPathFallbackQuery (k := k)

@[simp] theorem markovTransitionPathQueryOfAtom_path
    (start : Fin k) (tail : List (Fin k)) :
    markovTransitionPathQueryOfAtom (k := k)
        markovTransitionPathAtomName
        (markovTransitionPathAtomPattern start tail) =
      ⟨start, tail⟩ := by
  simp [markovTransitionPathQueryOfAtom]

/-- Public Xi surface for direct multi-step Markov path atoms. The rule sets are
empty: the semantics comes from the predictive chain, not additive rewrites. -/
def markovTransitionPathXiPLN :
    XiPLN
      (State := MarkovTransitionPathState k)
      (Query := MarkovTransitionPathQuery k) where
  queryOfAtom := markovTransitionPathQueryOfAtom (k := k)
  rulesE := ∅
  rulesS := ∅

@[simp] theorem markovTransitionPathXiPLN_queryOfAtom_path
    (start : Fin k) (tail : List (Fin k)) :
    (markovTransitionPathXiPLN (k := k)).queryOfAtom
        markovTransitionPathAtomName
        (markovTransitionPathAtomPattern start tail) =
      ⟨start, tail⟩ :=
  markovTransitionPathQueryOfAtom_path (k := k) start tail

/-- Extract the full Markov transition-count matrix from the additive WM carrier. -/
def markov_countsExtract (W : MarkovTransitionWMState k) : UniversalPrediction.TransCounts k :=
  ⟨fun prev next => (markov_rowExtract (k := k) W prev).counts next⟩

omit [NeZero k] in
@[simp] theorem markov_countsExtract_counts
    (W : MarkovTransitionWMState k) (prev next : Fin k) :
    (markov_countsExtract (k := k) W).counts prev next =
      (markov_rowExtract (k := k) W prev).counts next :=
  rfl

/-- On a word's transition multiset, `markov_countsExtract` recovers the summary
transition counts exactly. -/
theorem markov_countsExtract_transitionMultiset_eq_of_summary
    {k : ℕ}
    {xs : List (Fin k)}
    {c : UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum : UniversalPrediction.TransCounts.summary (k := k) xs = some (c, last)) :
    markov_countsExtract (k := k) (markov_transitionMultiset (k := k) xs) = c := by
  ext prev next
  rw [markov_countsExtract_counts]
  rw [markov_rowExtract_transitionMultiset_eq_rowEvidence_of_summary (k := k) hsum prev]
  simp [markov_rowEvidence]

/-- BinaryEvidence view of a predictive path probability. -/
def markovPathEvidenceOfProb (p : ℝ≥0∞) : BinaryEvidence :=
  ⟨p, 1 - p⟩

/-- Singleton mass semantics whose query mass is exactly the Markov predictive
chain. This is the honest non-additive carrier for path queries. -/
def markovPathMassSemantics
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (c : UniversalPrediction.TransCounts k) :
    MassSemantics (MarkovTransitionPathQuery k) where
  queryMass q := markovWMPosteriorChain hk prior q.start c q.tail
  totalMass := 1
  queryMass_le_total q := markovWMPosteriorChain_le_one (k := k) hk prior q.start c q.tail
  totalMass_ne_top := by simp

@[simp] theorem markovPathMassSemantics_queryProb
    {k : ℕ}
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (c : UniversalPrediction.TransCounts k) (q : MarkovTransitionPathQuery k) :
    (markovPathMassSemantics (k := k) hk prior c).queryProb q =
      markovWMPosteriorChain hk prior q.start c q.tail := by
  simp [MassSemantics.queryProb, markovPathMassSemantics]

@[simp] theorem markovPathMassSemantics_evidenceOfMasses
    {k : ℕ}
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (c : UniversalPrediction.TransCounts k) (q : MarkovTransitionPathQuery k) :
    (markovPathMassSemantics (k := k) hk prior c).evidenceOfMasses q =
      markovPathEvidenceOfProb (markovWMPosteriorChain hk prior q.start c q.tail) := by
  simp [MassSemantics.evidenceOfMasses, markovPathMassSemantics, markovPathEvidenceOfProb]

/-- Package a multiset WM state as a singleton mass semantics source for the
path-query surface. -/
def markovTransitionPathStateOfWM
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (W : MarkovTransitionWMState k) : MarkovTransitionPathState k :=
  {markovPathMassSemantics (k := k) hk prior (markov_countsExtract (k := k) W)}

/-- Direct atom-evidence semantics for a well-formed Markov path atom is the
BinaryEvidence view of the predictive chain mass. -/
theorem markovTransitionPathAtom_semE_eq_chainEvidence
    (R : Pattern → Pattern → Prop)
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (W : MarkovTransitionWMState k)
    (start : Fin k) (tail : List (Fin k)) :
    semE R
        (wmEvidenceAtomSemQ
          (markovTransitionPathStateOfWM (k := k) hk prior W)
          ((markovTransitionPathXiPLN (k := k)).queryOfAtom))
        (.atom markovTransitionPathAtomName)
        (markovTransitionPathAtomPattern start tail) =
      markovPathEvidenceOfProb
        (markovWMPosteriorChain hk prior start (markov_countsExtract (k := k) W) tail) := by
  rw [semE_atom_wmEvidenceAtomSemQ]
  rw [markovTransitionPathXiPLN_queryOfAtom_path (k := k) start tail]
  change MassState.evidence
      ({markovPathMassSemantics (k := k) hk prior (markov_countsExtract (k := k) W)} :
        MarkovTransitionPathState k)
      ⟨start, tail⟩ =
    markovPathEvidenceOfProb
      (markovWMPosteriorChain hk prior start (markov_countsExtract (k := k) W) tail)
  simpa [markovTransitionPathStateOfWM] using
    (MassState.evidence_singleton
      (markovPathMassSemantics (k := k) hk prior (markov_countsExtract (k := k) W))
      ⟨start, tail⟩)

/-- Strength-level semantics for a well-formed Markov path atom recovers the
predictive chain probability exactly. -/
theorem markovTransitionPathAtom_queryStrength_eq_chain
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (W : MarkovTransitionWMState k)
    (start : Fin k) (tail : List (Fin k)) :
    BinaryWorldModel.queryStrength
        (State := MarkovTransitionPathState k)
        (Query := MarkovTransitionPathQuery k)
        (markovTransitionPathStateOfWM (k := k) hk prior W)
        (((markovTransitionPathXiPLN (k := k)).queryOfAtom)
          markovTransitionPathAtomName
          (markovTransitionPathAtomPattern start tail)) =
      markovWMPosteriorChain hk prior start (markov_countsExtract (k := k) W) tail := by
  rw [markovTransitionPathXiPLN_queryOfAtom_path (k := k) start tail]
  simpa [markovTransitionPathStateOfWM] using
    (MassState.queryStrength_singleton_eq_queryProb
      (markovPathMassSemantics (k := k) hk prior (markov_countsExtract (k := k) W))
      ⟨start, tail⟩)

/-- Summary specialization: a path atom evaluated on the transition multiset of a
word depends only on the transition-count summary. -/
theorem markovTransitionPathAtom_queryStrength_transitionMultiset_eq_of_summary
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    {xs : List (Fin k)}
    {c : UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum : UniversalPrediction.TransCounts.summary (k := k) xs = some (c, last))
    (start : Fin k) (tail : List (Fin k)) :
    BinaryWorldModel.queryStrength
        (State := MarkovTransitionPathState k)
        (Query := MarkovTransitionPathQuery k)
        (markovTransitionPathStateOfWM (k := k) hk prior
          (markov_transitionMultiset (k := k) xs))
        (((markovTransitionPathXiPLN (k := k)).queryOfAtom)
          markovTransitionPathAtomName
          (markovTransitionPathAtomPattern start tail)) =
      markovWMPosteriorChain hk prior start c tail := by
  rw [markovTransitionPathAtom_queryStrength_eq_chain (k := k) hk prior
    (markov_transitionMultiset (k := k) xs) start tail]
  rw [markov_countsExtract_transitionMultiset_eq_of_summary (k := k) hsum]

abbrev bit0 : Fin 2 := ⟨0, by decide⟩
abbrev bit1 : Fin 2 := ⟨1, by decide⟩

/-- Concrete binary path atom for the transition path `0 → 0 → 1`. -/
def bit001Pattern : Pattern :=
  markovTransitionPathAtomPattern (k := 2) bit0 [bit0, bit1]

/-- Concrete binary path atom for the transition path `0 → 1 → 1`. -/
def bit011Pattern : Pattern :=
  markovTransitionPathAtomPattern (k := 2) bit0 [bit1, bit1]

@[simp] theorem bit001Pattern_query :
    ((markovTransitionPathXiPLN (k := 2)).queryOfAtom)
        markovTransitionPathAtomName bit001Pattern =
      ⟨bit0, [bit0, bit1]⟩ := by
  simp [bit001Pattern, markovTransitionPathXiPLN_queryOfAtom_path]

@[simp] theorem bit011Pattern_query :
    ((markovTransitionPathXiPLN (k := 2)).queryOfAtom)
        markovTransitionPathAtomName bit011Pattern =
      ⟨bit0, [bit1, bit1]⟩ := by
  simp [bit011Pattern, markovTransitionPathXiPLN_queryOfAtom_path]

/-- Binary example: the path atom `0 → 0 → 1` evaluates to the corresponding
two-step predictive chain on any summarized history. -/
theorem bit001_queryStrength_transitionMultiset_eq_of_summary
    (hk : 0 < 2) (prior : Fin 2 → DirichletParams 2)
    {xs : List (Fin 2)}
    {c : UniversalPrediction.TransCounts 2}
    {last : Fin 2}
    (hsum : UniversalPrediction.TransCounts.summary (k := 2) xs = some (c, last)) :
    BinaryWorldModel.queryStrength
        (State := MarkovTransitionPathState 2)
        (Query := MarkovTransitionPathQuery 2)
        (markovTransitionPathStateOfWM (k := 2) hk prior
          (markov_transitionMultiset (k := 2) xs))
        (((markovTransitionPathXiPLN (k := 2)).queryOfAtom)
          markovTransitionPathAtomName bit001Pattern) =
      markovWMPosteriorChain (k := 2) hk prior bit0 c [bit0, bit1] := by
  simpa [bit001Pattern] using
    markovTransitionPathAtom_queryStrength_transitionMultiset_eq_of_summary
      (k := 2) hk prior hsum bit0 [bit0, bit1]

/-- Binary example: the path atom `0 → 1 → 1` evaluates to the corresponding
two-step predictive chain on any summarized history. -/
theorem bit011_queryStrength_transitionMultiset_eq_of_summary
    (hk : 0 < 2) (prior : Fin 2 → DirichletParams 2)
    {xs : List (Fin 2)}
    {c : UniversalPrediction.TransCounts 2}
    {last : Fin 2}
    (hsum : UniversalPrediction.TransCounts.summary (k := 2) xs = some (c, last)) :
    BinaryWorldModel.queryStrength
        (State := MarkovTransitionPathState 2)
        (Query := MarkovTransitionPathQuery 2)
        (markovTransitionPathStateOfWM (k := 2) hk prior
          (markov_transitionMultiset (k := 2) xs))
        (((markovTransitionPathXiPLN (k := 2)).queryOfAtom)
          markovTransitionPathAtomName bit011Pattern) =
      markovWMPosteriorChain (k := 2) hk prior bit0 c [bit1, bit1] := by
  simpa [bit011Pattern] using
    markovTransitionPathAtom_queryStrength_transitionMultiset_eq_of_summary
      (k := 2) hk prior hsum bit0 [bit1, bit1]

end Mettapedia.Logic.MarkovPathXi
