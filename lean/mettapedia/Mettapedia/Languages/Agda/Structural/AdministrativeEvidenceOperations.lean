import Mettapedia.Languages.Agda.Structural.AdministrativeTypedSubstitution
import Mettapedia.Languages.Agda.Structural.AdministrativeContextRegularity
import Mettapedia.Languages.Agda.Structural.AdministrativeTypeViews
import Mettapedia.Languages.Agda.Structural.StaticEvidenceOperations

/-!
# Derived evidence operations on administrative static trees

Every operation is supplied by a checked fold on the combined presentation.
The canonical algebra is its actual restriction, so its recursive children
may contain spine-generated typing trees. This instance adds no rule and
assumes no preservation or normalization theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.TypeTheory

noncomputable def administrativeOperations : Statics.EvidenceOperations CoreDerivation where
  algebra := canonicalAlgebra (IndexedPolynomial.Algebra.initial presentation.polynomial)
  renameEvidence := CoreDerivation.renaming
  substituteEvidence := CoreDerivation.substitution
  contexts := fun tree => Derivation.contextRegularity tree
  typeViews := fun tree => Derivation.typeViews tree

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
