import Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

/-!
# Structural algebra for generated Metamath proof forests

The reverse normal-proof fold needs to concatenate and split source-pinned
forests without forgetting their dependent formula indices.  This file keeps
the original trees themselves: append is structural, split reconstructs the
input forest exactly, and singleton inversion extracts the stored tree.

The accompanying label and raw-erasure equations make the authored order
observable.  No runtime provenance or whole-proof acceptance claim is made.
-/

namespace Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection

/-! ## Ordered runtime images -/

@[simp] theorem runtimeFormulaArray_append
    (left right : List ConstantHeadedFormula) :
    runtimeFormulaArray (left ++ right) =
      runtimeFormulaArray left ++ runtimeFormulaArray right := by
  simp [runtimeFormulaArray]

/-! ## Exact forest append -/

/-- Concatenate two source-pinned forests while retaining the exact appended
formula-list index. -/
def GeneratedProvesForest.append
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (left : GeneratedProvesForest projection target leftFormulas)
    (right : GeneratedProvesForest projection target rightFormulas) :
    GeneratedProvesForest projection target (leftFormulas ++ rightFormulas) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (tail.append right)

@[simp] theorem GeneratedProvesForest.labels_append
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (left : GeneratedProvesForest projection target leftFormulas)
    (right : GeneratedProvesForest projection target rightFormulas) :
    (left.append right).labels = left.labels ++ right.labels := by
  cases left with
  | nil => rfl
  | cons head tail =>
      simp [GeneratedProvesForest.append, GeneratedProvesForest.labels,
        GeneratedProvesForest.labels_append tail right, List.append_assoc]
termination_by sizeOf left

@[simp] theorem GeneratedProvesForest.canonicalRawProofs_append
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (left : GeneratedProvesForest projection target leftFormulas)
    (right : GeneratedProvesForest projection target rightFormulas) :
    (left.append right).canonicalRawProofs =
      left.canonicalRawProofs ++ right.canonicalRawProofs := by
  cases left with
  | nil => rfl
  | cons head tail =>
      simp [GeneratedProvesForest.append,
        GeneratedProvesForest.canonicalRawProofs,
        GeneratedProvesForest.canonicalRawProofs_append tail right]
termination_by sizeOf left

/-- The native derivation-list erasure of structural append is the exact
ordered append of the two original erasures. -/
theorem GeneratedProvesForest.erase_toDerivationList_append
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (left : GeneratedProvesForest projection target leftFormulas)
    (right : GeneratedProvesForest projection target rightFormulas) :
    ((left.append right).toDerivationList hprojection).erase =
      (left.toDerivationList hprojection).erase ++
        (right.toDerivationList hprojection).erase := by
  rw [GeneratedProvesForest.erase_toDerivationList,
    GeneratedProvesForest.canonicalRawProofs_append,
    GeneratedProvesForest.erase_toDerivationList,
    GeneratedProvesForest.erase_toDerivationList]

/-! ## Proof-relevant exact split -/

/-- An exact split keeps both original-order subforests and an equality saying
that structural append reconstructs the supplied forest. -/
structure GeneratedProvesForest.ExactSplit
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (leftIndex rightIndex : List ConstantHeadedFormula)
    (forest : GeneratedProvesForest projection target
      (leftIndex ++ rightIndex)) where
  leftForest : GeneratedProvesForest projection target leftIndex
  rightForest : GeneratedProvesForest projection target rightIndex
  append_eq : leftForest.append rightForest = forest

/-- Split at the formula-list index boundary.  Every tree and every proof field
is reused from the input forest. -/
def GeneratedProvesForest.splitExact
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (leftIndex rightIndex : List ConstantHeadedFormula)
    (forest : GeneratedProvesForest projection target
      (leftIndex ++ rightIndex)) :
    GeneratedProvesForest.ExactSplit leftIndex rightIndex forest :=
  match leftIndex, forest with
  | [], forest =>
      { leftForest := .nil
        rightForest := forest
        append_eq := rfl }
  | _ :: _, .cons head tail =>
      let splitTail := tail.splitExact _ rightIndex
      { leftForest := .cons head splitTail.leftForest
        rightForest := splitTail.rightForest
        append_eq := by
          simp only [GeneratedProvesForest.append]
          rw [splitTail.append_eq] }

theorem GeneratedProvesForest.ExactSplit.labels_eq
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftIndex rightIndex : List ConstantHeadedFormula}
    {forest : GeneratedProvesForest projection target
      (leftIndex ++ rightIndex)}
    (split : GeneratedProvesForest.ExactSplit leftIndex rightIndex forest) :
    split.leftForest.labels ++ split.rightForest.labels = forest.labels := by
  rw [← GeneratedProvesForest.labels_append, split.append_eq]

theorem GeneratedProvesForest.ExactSplit.canonicalRawProofs_eq
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftIndex rightIndex : List ConstantHeadedFormula}
    {forest : GeneratedProvesForest projection target
      (leftIndex ++ rightIndex)}
    (split : GeneratedProvesForest.ExactSplit leftIndex rightIndex forest) :
    split.leftForest.canonicalRawProofs ++
        split.rightForest.canonicalRawProofs =
      forest.canonicalRawProofs := by
  rw [← GeneratedProvesForest.canonicalRawProofs_append, split.append_eq]

/-! ## Singleton and emptiness inversion -/

/-- Extract the one stored tree from a forest whose formula index is a
singleton. -/
def GeneratedProvesForest.singletonTree
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target [formula]) :
    GeneratedProvesTree projection target formula :=
  match forest with
  | .cons tree .nil => tree

@[simp] theorem GeneratedProvesForest.singleton_reconstruct
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target [formula]) :
    (.cons forest.singletonTree .nil :
      GeneratedProvesForest projection target [formula]) = forest := by
  cases forest with
  | cons tree tail => cases tail; rfl

/-- Forest labels are empty exactly when the dependent formula index is empty.
The forward direction uses the existing fact that every stored tree emits at
least one authored label. -/
theorem GeneratedProvesForest.labels_eq_nil_iff
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas) :
    forest.labels = [] ↔ formulas = [] := by
  cases forest with
  | nil => simp [GeneratedProvesForest.labels]
  | cons head tail =>
      constructor
      · intro hempty
        have hhead : head.labels = [] :=
          (List.append_eq_nil_iff.mp hempty).1
        exact (head.labels_ne_nil hhead).elim
      · intro hformulas
        simp at hformulas

/-! ## Positive and negative boundaries -/

example {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (left : GeneratedProvesForest projection target leftFormulas)
    (right : GeneratedProvesForest projection target rightFormulas) :
    (left.append right).canonicalRawProofs =
      left.canonicalRawProofs ++ right.canonicalRawProofs := by
  exact left.canonicalRawProofs_append right

example {projection : PrefixProjection} {target : ValidatedPresentation}
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target
      (leftFormulas ++ rightFormulas)) :
    let split := forest.splitExact leftFormulas rightFormulas
    split.leftForest.append split.rightForest = forest := by
  exact (forest.splitExact leftFormulas rightFormulas).append_eq

example {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target [formula]) :
    (.cons forest.singletonTree .nil :
      GeneratedProvesForest projection target [formula]) = forest := by
  exact forest.singleton_reconstruct

example {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula} {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target (formula :: formulas)) :
    forest.labels ≠ [] := by
  intro hempty
  have hindex := forest.labels_eq_nil_iff.mp hempty
  contradiction

end Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
