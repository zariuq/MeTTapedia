import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Pack
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Laws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Simple
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Identity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Declaration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Indices
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.SimpleDeclaration

/-!
# Inductive families in the normalization model

* `Pack`: the family pack, the reducible terms and equalities of an inductive family read
  at its parameters, defined at all indices at once.
* `Laws`: the laws each case of the relation asks of a pack: normal forms, reflexivity, the
  ends of an equality, symmetry, transitivity, transfer between reducibly equal indices,
  renaming along a world, expansion, reflection of neutral terms, escape.
* `Transport`: transport between two readings, for irrelevance.
* `Simple`: a simple inductive type is a family with no parameters and no indices; its pack
  is the family pack at that reading.
* `Identity`: the identity type is a family with one constructor with one field; its pack
  is the family pack at that reading.
* `Declaration`: the schema of declared families with telescopes, their declared types, and
  their reading at given parameters.
* `Indices`: reducible equality at simple inductive index types is rigid on constructors.
* `SimpleDeclaration`: a simple inductive type as a declared family; its pack is the family
  pack at its declaration.
-/
