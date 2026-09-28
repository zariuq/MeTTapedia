import Mettapedia.Languages.Agda.Adequacy.StaticQualification
import Mettapedia.Languages.Agda.Structural.AdministrativeCompatibleControls
import Mettapedia.Languages.Agda.Structural.AdministrativeSpineLinearizationControls
import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationComponentControls
import Mettapedia.Languages.Agda.Adequacy.AdministrativePresentationControls

/-!
# Compatible preservation for the finite native static fragment

The recursive administrative static presentation supports both binding beta
roots and every compatible position of the actual computation presentation.
The source Pi-component theorem enters through the adequacy bridge; structural
generation, substitution, and the compatible fold remain source-independent.
Terms keep their original raw result type. Spine action endpoints require
formed input, while conditional spine equality retains its weaker premise.

Computation trees and finite paths produce native equality and typing evidence.
The original histories and the step fields of certificates retain occurrence
positions; no inverse from the produced static evidence to those histories is
asserted. This covers the finite Set/Pi fragment, not full Agda declarations,
normalization, a complete conversion checker, or efficient proof reconstruction.
-/
