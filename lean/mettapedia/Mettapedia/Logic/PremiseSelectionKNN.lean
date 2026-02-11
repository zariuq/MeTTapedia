import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# k-NN Premise Selection (features + IDF + MaSh instance)

This module defines a minimal, formal k-nearest-neighbors (k-NN) scoring scheme for
premise selection. It separates:

* feature extraction `F : Fact -> Finset Feature`
* inverse document frequency (IDF) weighting
* k-NN nearness and relevance scoring

The MaSh k-NN used in Sledgehammer is captured as a specific instance of these
definitions, with IDF weights and the MaSh relevance formula.

We keep the definitions finite and structural to make later PLN bridges precise.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical

/-! ## Feature sets and IDF weights -/

abbrev FeatureSet (Fact Feature : Type*) := Fact -> Finset Feature

abbrev DepSet (Fact : Type*) := Fact -> Finset Fact

def featureCount {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (F : FeatureSet Fact Feature) (f : Feature) : Nat :=
  (facts.filter (fun phi => f ∈ F phi)).card

/-- IDF weight as in MaSh: log(|Phi| / |{phi in Phi | f in F(phi)}|).
    We return 0 when the feature does not occur in the fact set. -/
noncomputable def idfWeight {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (F : FeatureSet Fact Feature) (f : Feature) : ℝ :=
  let n := featureCount facts F f
  if n = 0 then 0 else
    Real.log ((facts.card : ℝ) / (n : ℝ))

/-! ## k-NN nearness and relevance -/

/-- Nearness of two facts based on shared features. `tau1` is a (typically integer)
    exponent parameter. -/
noncomputable def knnNear {Fact Feature : Type*} [DecidableEq Feature]
    (F : FeatureSet Fact Feature) (w : Feature -> ℝ) (tau1 : Nat)
    (phi chi : Fact) : ℝ :=
  Finset.sum (F phi ∩ F chi) (fun f => (w f) ^ tau1)

/-- Top-k elements by descending score. Ties are broken by the underlying list order. -/
noncomputable def topK {Fact : Type*} [DecidableEq Fact]
    (facts : Finset Fact) (k : Nat) (score : Fact -> ℝ) : Finset Fact :=
  ((List.insertionSort (fun a b => score b ≤ score a) facts.toList).take k).toFinset

/-- k-NN relevance score given an explicit neighbor set `N`. -/
noncomputable def knnRelevance {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ)
    (deps : DepSet Fact) (tau2 : ℝ) (phi : Fact) : ℝ :=
  let depTerm :=
    Finset.sum N (fun chi =>
      if phi ∈ deps chi then
        near chi goal / ((deps chi).card : ℝ)
      else 0)
  if phi ∈ N then
    tau2 * depTerm + near phi goal
  else 0

/-- k-NN relevance using the top-k neighbors selected by nearness. -/
noncomputable def knnScoreTopK {Fact : Type*} [DecidableEq Fact]
    (facts : Finset Fact) (k : Nat) (goal : Fact)
    (near : Fact -> Fact -> ℝ) (deps : DepSet Fact) (tau2 : ℝ) (phi : Fact) : ℝ :=
  let N := topK facts k (fun chi => near chi goal)
  knnRelevance goal N near deps tau2 phi

/-! ## MaSh instance -/

/-- MaSh nearness: shared-feature sum with IDF weights and exponent `tau1`. -/
noncomputable def mashNear {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (F : FeatureSet Fact Feature) (tau1 : Nat)
    (phi chi : Fact) : ℝ :=
  knnNear F (idfWeight facts F) tau1 phi chi

/-- MaSh k-NN relevance score with fixed k (the variable-k extension is algorithmic). -/
noncomputable def mashScoreTopK {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (k : Nat)
    (F : FeatureSet Fact Feature) (deps : DepSet Fact)
    (tau1 : Nat) (tau2 : ℝ) (goal phi : Fact) : ℝ :=
  knnScoreTopK facts k goal (mashNear facts F tau1) deps tau2 phi

lemma mashScoreTopK_is_knn {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (k : Nat)
    (F : FeatureSet Fact Feature) (deps : DepSet Fact)
    (tau1 : Nat) (tau2 : ℝ) (goal phi : Fact) :
    mashScoreTopK facts k F deps tau1 tau2 goal phi =
      knnScoreTopK facts k goal (mashNear facts F tau1) deps tau2 phi := rfl

/-- Default MaSh parameters from the paper. -/
def mashTau1 : Nat := 6

def mashTau2 : ℝ := 2.7

/-! ## Minimal examples (positive and negative) -/

section Examples

def exFeatures : FeatureSet Bool Bool
  | true => {true}
  | false => {false}

def exWeight : Bool -> ℝ := fun _ => 2

example : knnNear exFeatures exWeight 3 true true = (2 : ℝ) ^ 3 := by
  simp [knnNear, exFeatures, exWeight]

example : knnNear exFeatures exWeight 3 true false = 0 := by
  simp [knnNear, exFeatures, exWeight]

end Examples

end Mettapedia.Logic.PremiseSelection
