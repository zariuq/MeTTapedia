import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalStopAlignment

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Root alignment does yield canonical equality of the two patterns. -/
theorem fable_canonicalRootAligned_canonicalize_eq
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (aligned : CanonicalRootAligned declaration left right) :
    canonicalize declaration left = canonicalize declaration right :=
  (canonicalStopAligned_of_root_aligned declaration aligned).canonicalize_eq
    declaration (fun given => given.1.2)

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.fable_canonicalRootAligned_canonicalize_eq
