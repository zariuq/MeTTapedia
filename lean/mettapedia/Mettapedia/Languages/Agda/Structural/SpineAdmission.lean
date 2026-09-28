import Mettapedia.Languages.Agda.Structural.SpineTypedSubstitution
import Mettapedia.Languages.Agda.Structural.StaticAdmission

/-!
# Contextual admission by combined static derivations

The combined fixed point supplies the canonical constructor algebra and the
proved typed substitution operation required by contextual admission. Thus
administrative elimination terms can be admitted using their actual typing
trees. Formation and substitution evidence remain in companion fibres; the
category laws concern the supported, unquotiented raw syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics

open Mettapedia.TypeTheory
open Mettapedia.GSLT.Core.ContextualLadder

/-- Canonical constructors with every recursive child in the combined family. -/
noncomputable def coreAlgebra :
    IndexedPolynomial.Algebra Statics.presentation.polynomial (fun _ j => CoreDerivation j) :=
  canonicalAlgebra (IndexedPolynomial.Algebra.initial presentation.polynomial)

/-- Admission uses actual combined formation, typing, and variable-image trees. -/
noncomputable def spineAdmission : CwfDerivations Statics.rawCwf :=
  Statics.admissionData coreAlgebra CoreDerivation.substitution

/-- Formed combined contexts and supported typed substitutions, with their
terminal empty context. This does not identify different derivation histories. -/
noncomputable def spineCwf : CwfWithTerminal :=
  CwfDerivations.admittedWithTerminal ContextGeometry.rawAgdaTelescopeCwfWithTerminal
    spineAdmission (includeCanonical Statics.Derivation.empty)
    (fun _ formed => Statics.TypedSubstitution.empty coreAlgebra formed)

end Mettapedia.Languages.Agda.Structural.SpineStatics
