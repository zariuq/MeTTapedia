import Mettapedia.Languages.Agda.Structural.SpineTypedSubstitution
import Mettapedia.Languages.Agda.Structural.SpineContextRegularity
import Mettapedia.Languages.Agda.Structural.SpineTypeViews
import Mettapedia.Languages.Agda.Structural.StaticEvidenceOperations

/-!
# Instantiating shared derived operations with combined spine evidence

Every operation is supplied by a checked fold on the combined presentation.
The canonical algebra is its actual restriction, so its recursive children
may contain spine-generated typing trees. This instance adds no rule and
assumes no preservation or normalization theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics

open Mettapedia.TypeTheory

noncomputable def spineOperations : Statics.EvidenceOperations CoreDerivation where
  algebra := canonicalAlgebra (IndexedPolynomial.Algebra.initial presentation.polynomial)
  renameEvidence := CoreDerivation.renaming
  substituteEvidence := CoreDerivation.substitution
  contexts := fun tree => Derivation.contextRegularity tree
  typeViews := fun tree => Derivation.typeViews tree

end Mettapedia.Languages.Agda.Structural.SpineStatics
