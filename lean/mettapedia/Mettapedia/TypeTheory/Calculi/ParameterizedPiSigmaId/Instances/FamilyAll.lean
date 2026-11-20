import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectors
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExpressions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectorsEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExpressionsLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectorsEliminatorExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectorsLaws

/-!
# Declared inductive families: instances

* `FamilyVectors`: vectors, a family with a type parameter, indexed by their length; their
  canonical forms at `zero`, at a successor, and at a variable length.
* `FamilyExpressions`: typed expressions, indexed by their type; several constructors at one
  index and a constructor at every index; their canonical forms at a variable type and at
  the two closed types.
* `FamilyVectorsEliminator`: the dependent eliminator of vectors and its computation rules as
  a root computation meeting the shape obligations.
* `FamilyExamples`: a concrete setting with the families declared, and constructor elements
  that are reducible.
* `FamilyExpressionsLaws`: the hypotheses of the family pack's laws hold for expressions.
* `FamilyVectorsEliminatorExamples`: the eliminator's declared type is a type, and the package
  with its rules is a setting; an extension is a reducible vector.
* `FamilyVectorsLaws`: the hypotheses of the family pack's laws hold for vectors.
-/
