import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectors
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsLookup
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsHead
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsCoercion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsIdentity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsGeneralFamily

/-!
# Indexed families with eliminators in the normalization model

One rule package over the cumulative tower, with every hypothesis of the normalization model
proved, and the programs that use it.

* **The package** (`TowerVectors`): numbers, the unit and the empty type, the family of vectors
  with its dependent eliminator, addition computing in conversion, the order on the numbers with
  the finite types, and the identity eliminator. Vectors and the order are families declared by
  recursion on their index; the model interprets them by its cases for the unit type, the empty
  type and dependent pair types. The declarations hold at every generic equality with the laws.
* **Conversion** (`TowerVectorsConversion`): the conversion algorithm is complete for the
  package and the typed equality is decided; where conversion stops, by separating theorems.
* **Programs by the eliminators** (`TowerVectorsPrograms`, `TowerVectorsHead`,
  `TowerVectorsLookup`): `append` with both equations, typed at `vec A (add n m)`; `head`, by
  projection and by the eliminator with a motive computed from the length; `lookup` by a finite
  index with its two equations; the empty type and `fin zero` have no closed term.
* **Across an equation that conversion does not see** (`TowerVectorsCoercion`,
  `TowerVectorsIdentity`): a coercion `vec A (add n zero) → vec A n` by recursion on the length;
  `add n zero = n` proved by induction, and the transport of vectors along it.
* **A general indexed family** (`TowerVectorsGeneralFamily`): a family with a constructor at an
  index that is not a pattern, as a dependent pair type with an identity constraint, with its
  dependent eliminator and computation rule.

The family of vectors is a recursive family, not an inductive family with constructors of its
own: its type former is not injective at length zero, and its eliminator unfolds on every vector
of a successor length. Both are proved in `TowerVectors`.
-/
